// Lean compiler output
// Module: Lean.Elab.ConfigEval.Instances
// Imports: Lean.Elab.ConfigEval.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_int_dec_le, lean_int_neg,
    lean_int_neg_succ_of_nat, lean_name_eq, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_to_int, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_unzip___redArg;
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNameLit_x3f, l_Lean_TSyntax_getNat, l_Lean_TSyntax_getString,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::ConfigEval::Basic::{
    initialize_Lean_Elab_ConfigEval_Basic,
    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens,
    l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg,
    runtime_initialize_Lean_Elab_ConfigEval_Basic,
};
use crate::r#gen::Lean::Elab::ConfigEval::Types::l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_addTermInfo_x27;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_int_x3f, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_Expr_nat_x3f, l_Lean_Expr_rawNatLit_x3f, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppB,
    l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkStrLit,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::ToExpr::{
    l___private_Lean_ToExpr_0__Lean_Name_toExprAux, l_Lean_instToExprInt_mkNat,
};
use crate::r#gen::Lean::Util::Recognizers::l_Lean_Expr_name_x3f;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value:
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value)
            as *mut leanh::LeanObject,
        9255189395584251158 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__0_value)
            as *mut leanh::LeanObject,
        12882480457794858234 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value)
            as *mut leanh::LeanObject,
        15761733860085307253 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__4_value)
            as *mut leanh::LeanObject,
        6560861498103128555 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 111, 116, 73, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__14_value)
            as *mut leanh::LeanObject,
        14183307858573822893 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__7_value)
            as *mut leanh::LeanObject,
        8044760892103251616 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value:
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
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value:
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
    m_data: [110, 117, 109, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__4_value)
            as *mut leanh::LeanObject,
        6110315075117401315 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__5_value)
            as *mut leanh::LeanObject,
        9626815015619986526 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__6_value)
            as *mut leanh::LeanObject,
        17185717442815859305 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__11_value)
            as *mut leanh::LeanObject,
        6362876895233142233 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 101, 114, 109, 45, 95, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__14_value)
            as *mut leanh::LeanObject,
        9498589259807162189 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [83, 116, 114, 105, 110, 103, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__0_value)
            as *mut leanh::LeanObject,
        3136308715950998022 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value:
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
    m_data: [115, 116, 114, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__4_value)
            as *mut leanh::LeanObject,
        9232979286016572671 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__7_value) as *mut leanh::LeanObject,7870113334857981723 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__14_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        100, 111, 117, 98, 108, 101, 81, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value:
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
    m_data: [78, 97, 109, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__0_value)
            as *mut leanh::LeanObject,
        13306843946249674491 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__4_value)
            as *mut leanh::LeanObject,
        9368229134555052249 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value:
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
    m_data: [115, 111, 109, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [79, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        18184376426117065311 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value
        ) as *mut leanh::LeanObject,
        17416048715816169289 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value:
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
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__5_value
        ) as *mut leanh::LeanObject,
        12966880221525079621 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        15308379890181982757 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        18184376426117065311 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__3_value
        ) as *mut leanh::LeanObject,
        9480010471355609749 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__1_value) as *mut leanh::LeanObject,8614124190858717794 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 101, 114, 109, 91, 95, 93, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        11666683425613976406 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value:
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
    m_data: [110, 105, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        18135193680607614554 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7_value:
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
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        8749134177695247953 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 111, 65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value:
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
    m_data: [116, 101, 114, 109, 35, 91, 95, 44, 93, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        17856333342802343749 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value:
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
    m_data: [80, 114, 111, 100, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        15289851429949568889 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 117, 112, 108, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        15644373471618144447 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
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
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__6_value)
            as *mut leanh::LeanObject,
        7306243862518720553 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__8_value)
            as *mut leanh::LeanObject,
        9871775667037945883 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [109, 107, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        15289851429949568889 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        6466355875042130293 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value:
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
    m_data: [68, 97, 116, 97, 86, 97, 108, 117, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [111, 102, 66, 111, 111, 108, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value)
            as *mut leanh::LeanObject,
        13555476944791110774 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__2_value)
            as *mut leanh::LeanObject,
        12272190304438458363 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [111, 102, 78, 97, 109, 101, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value)
            as *mut leanh::LeanObject,
        13555476944791110774 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__7_value)
            as *mut leanh::LeanObject,
        16803091093357105251 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 102, 83, 116, 114, 105, 110, 103, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value)
            as *mut leanh::LeanObject,
        13555476944791110774 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__9_value)
            as *mut leanh::LeanObject,
        12519407092731657178 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 73, 110, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value)
            as *mut leanh::LeanObject,
        13555476944791110774 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__12_value)
            as *mut leanh::LeanObject,
        1326771483907695317 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value)
            as *mut leanh::LeanObject,
        13555476944791110774 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value)
            as *mut leanh::LeanObject,
        14715853951479936487 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalTerm_instBool: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalTerm_instNat: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalTerm_instInt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalTerm_instString: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalTerm_instName: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__0_value)
            as *mut leanh::LeanObject,
        13555476944791110774 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalTerm_instDataValue: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [96, 46, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 101, 103, 83, 117, 99, 99, 0],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__0_value)
            as *mut leanh::LeanObject,
        14511501467246783669 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__0_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__14_value)
            as *mut leanh::LeanObject,
        6667203625087222464 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        18184376426117065311 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        4893146552088433753 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0_value:
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
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32,
        116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        8749134177695247953 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__10_value)
            as *mut leanh::LeanObject,
        15116455438679371901 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0_value) as *mut leanh::LeanObject,9582258842178272501 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        8414467900391110369 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalExpr_instBool: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalExpr_instNat: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalExpr_instInt: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalExpr_instString: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_ConfigEval_EvalExpr_instName: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value:
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
    m_fun: l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__0_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_ConfigEval_EvalExpr_instDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ConfigEval_EvalExpr_instDataValue___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4036_ = leanh::lean_box(0);
    v___x_4037_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4038_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4038_, 0, v___x_4037_);
    leanh::lean_ctor_set(v___x_4038_, 1, v___x_4036_);
    return v___x_4038_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4040_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___closed__0);
    v___x_4041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4041_, 0, v___x_4040_);
    return v___x_4041_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg___boxed(
    mut v___y_4042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4043_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
    return v_res_4043_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(
    mut v_00_u03b1_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
    mut v___y_4047_: *mut leanh::LeanObject,
    mut v___y_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4052_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
    return v___x_4052_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___boxed(
    mut v_00_u03b1_4053_: *mut leanh::LeanObject,
    mut v___y_4054_: *mut leanh::LeanObject,
    mut v___y_4055_: *mut leanh::LeanObject,
    mut v___y_4056_: *mut leanh::LeanObject,
    mut v___y_4057_: *mut leanh::LeanObject,
    mut v___y_4058_: *mut leanh::LeanObject,
    mut v___y_4059_: *mut leanh::LeanObject,
    mut v___y_4060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4061_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0(v_00_u03b1_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
    leanh::lean_dec(v___y_4059_);
    leanh::lean_dec_ref(v___y_4058_);
    leanh::lean_dec(v___y_4057_);
    leanh::lean_dec_ref(v___y_4056_);
    leanh::lean_dec(v___y_4055_);
    leanh::lean_dec_ref(v___y_4054_);
    return v_res_4061_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4065_ = leanh::lean_box(0);
    v___x_4066_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1;
    v___x_4067_ = l_Lean_mkConst(v___x_4066_, v___x_4065_);
    return v___x_4067_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4068_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2,
    );
    v___x_4069_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4069_, 0, v___x_4068_);
    return v___x_4069_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4074_ = leanh::lean_box(0);
    v___x_4075_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5;
    v___x_4076_ = l_Lean_mkConst(v___x_4075_, v___x_4074_);
    return v___x_4076_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4081_ = leanh::lean_box(0);
    v___x_4082_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8;
    v___x_4083_ = l_Lean_mkConst(v___x_4082_, v___x_4081_);
    return v___x_4083_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(
    mut v_a_4097_: *mut leanh::LeanObject,
    mut v_a_4098_: *mut leanh::LeanObject,
    mut v_a_4099_: *mut leanh::LeanObject,
    mut v_a_4100_: *mut leanh::LeanObject,
    mut v_a_4101_: *mut leanh::LeanObject,
    mut v_a_4102_: *mut leanh::LeanObject,
    mut v_a_4103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4106_: u8 = 0;
    let mut v___y_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4110_: u8 = 0;
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut v_unused_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4130_: u8 = 0;
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4134_: u8 = 0;
    let mut v_a_4136_: u8 = 0;
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4139_: u8 = 0;
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4146_: u8 = 0;
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4150_: u8 = 0;
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4156_: u8 = 0;
    let mut v___y_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4158_: u8 = 0;
    let mut v___y_4159_: u8 = 0;
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: u8 = 0;
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: u8 = 0;
    let mut v___x_4166_: u8 = 0;
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4169_: u8 = 0;
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: u8 = 0;
    let mut v___x_4175_: u8 = 0;
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_4097_);
                v___x_4151_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_a_4097_,
                    );
                v___x_4152_ = l_Lean_Syntax_getId(v___x_4151_);
                v_id_4153_ = lean_erase_macro_scopes(v___x_4152_);
                v___x_4154_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__10;
                v___x_4175_ = lean_name_eq(v_id_4153_, v___x_4154_);
                if v___x_4175_ == 0 {
                    v___x_4176_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5;
                    v___x_4177_ = lean_name_eq(v_id_4153_, v___x_4176_);
                    v___y_4169_ = v___x_4177_;
                    state = 12;
                    continue;
                } else {
                    v___y_4169_ = v___x_4175_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_4108_ = lean_st_ref_get(v_a_4103_);
                v_infoState_4109_ = leanh::lean_ctor_get(v___x_4108_, 7);
                leanh::lean_inc_ref(v_infoState_4109_);
                leanh::lean_dec(v___x_4108_);
                v_enabled_4110_ = leanh::lean_ctor_get_uint8(
                    v_infoState_4109_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_4109_);
                v___x_4111_ = leanh::lean_box((v___y_4106_) as usize);
                leanh::lean_inc_ref(v___y_4107_);
                v___x_4112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4112_, 0, v___x_4111_);
                leanh::lean_ctor_set(v___x_4112_, 1, v___y_4107_);
                if v_enabled_4110_ == 0 {
                    leanh::lean_dec(v_a_4097_);
                    v___x_4113_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4113_, 0, v___x_4112_);
                    return v___x_4113_;
                } else {
                    v___x_4114_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3,
                    );
                    v___x_4115_ = leanh::lean_box(0);
                    v___x_4116_ = leanh::lean_box(0);
                    v___x_4117_ = 0;
                    leanh::lean_inc_ref(v___y_4107_);
                    v___x_4118_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_a_4097_,
                        v___y_4107_,
                        v___x_4114_,
                        v___x_4115_,
                        v___x_4116_,
                        v___x_4117_,
                        v___x_4117_,
                        v_a_4098_,
                        v_a_4099_,
                        v_a_4100_,
                        v_a_4101_,
                        v_a_4102_,
                        v_a_4103_,
                    );
                    if leanh::lean_obj_tag(v___x_4118_) == 0 {
                        v_isSharedCheck_4125_ =
                            (!leanh::lean_is_exclusive(v___x_4118_)) as u8;
                        if v_isSharedCheck_4125_ == 0 {
                            v_unused_4126_ = leanh::lean_ctor_get(v___x_4118_, 0);
                            leanh::lean_dec(v_unused_4126_);
                            v___x_4120_ = v___x_4118_;
                            v_isShared_4121_ = v_isSharedCheck_4125_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4118_);
                            v___x_4120_ = leanh::lean_box(0);
                            v_isShared_4121_ = v_isSharedCheck_4125_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_4112_, 2);
                        v_a_4127_ = leanh::lean_ctor_get(v___x_4118_, 0);
                        v_isSharedCheck_4134_ =
                            (!leanh::lean_is_exclusive(v___x_4118_)) as u8;
                        if v_isSharedCheck_4134_ == 0 {
                            v___x_4129_ = v___x_4118_;
                            v_isShared_4130_ = v_isSharedCheck_4134_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4127_);
                            leanh::lean_dec(v___x_4118_);
                            v___x_4129_ = leanh::lean_box(0);
                            v_isShared_4130_ = v_isSharedCheck_4134_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_4121_ == 0 {
                    leanh::lean_ctor_set(v___x_4120_, 0, v___x_4112_);
                    v___x_4123_ = v___x_4120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4112_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4123_;
            }
            4 => {
                if v_isShared_4130_ == 0 {
                    v___x_4132_ = v___x_4129_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4133_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
                    v___x_4132_ = v_reuseFailAlloc_4133_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4132_;
            }
            6 => {
                v___x_4137_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__6,
                );
                v___y_4106_ = v_a_4136_;
                v___y_4107_ = v___x_4137_;
                state = 1;
                continue;
            }
            7 => {
                if v_a_4139_ == 0 {
                    v___x_4140_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__9,
                    );
                    v___y_4106_ = v_a_4139_;
                    v___y_4107_ = v___x_4140_;
                    state = 1;
                    continue;
                } else {
                    v_a_4136_ = v_a_4139_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v_a_4143_ = leanh::lean_ctor_get(v___y_4142_, 0);
                v_isSharedCheck_4150_ = (!leanh::lean_is_exclusive(v___y_4142_)) as u8;
                if v_isSharedCheck_4150_ == 0 {
                    v___x_4145_ = v___y_4142_;
                    v_isShared_4146_ = v_isSharedCheck_4150_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4143_);
                    leanh::lean_dec(v___y_4142_);
                    v___x_4145_ = leanh::lean_box(0);
                    v_isShared_4146_ = v_isSharedCheck_4150_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4146_ == 0 {
                    v___x_4148_ = v___x_4145_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
                    v___x_4148_ = v_reuseFailAlloc_4149_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4148_;
            }
            11 => {
                if v___y_4159_ == 0 {
                    v___x_4160_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15;
                    leanh::lean_inc(v___x_4151_);
                    v___x_4161_ = l_Lean_Syntax_isOfKind(v___x_4151_, v___x_4160_);
                    if v___x_4161_ == 0 {
                        leanh::lean_dec(v___x_4151_);
                        leanh::lean_dec(v_a_4097_);
                        v___x_4162_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                        v___y_4142_ = v___x_4162_;
                        state = 8;
                        continue;
                    } else {
                        v___x_4163_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4164_ = l_Lean_Syntax_getArg(v___x_4151_, v___x_4163_);
                        leanh::lean_dec(v___x_4151_);
                        v___x_4165_ = l_Lean_Syntax_matchesIdent(v___x_4164_, v___x_4154_);
                        if v___x_4165_ == 0 {
                            leanh::lean_inc(v___y_4157_);
                            v___x_4166_ = l_Lean_Syntax_matchesIdent(v___x_4164_, v___y_4157_);
                            leanh::lean_dec(v___x_4164_);
                            if v___x_4166_ == 0 {
                                leanh::lean_dec(v_a_4097_);
                                v___x_4167_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                                v___y_4142_ = v___x_4167_;
                                state = 8;
                                continue;
                            } else {
                                v_a_4139_ = v___x_4165_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_4164_);
                            v_a_4139_ = v___y_4158_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_4151_);
                    v_a_4139_ = v___y_4156_;
                    state = 7;
                    continue;
                }
            }
            12 => {
                v___x_4170_ = 1;
                if v___y_4169_ == 0 {
                    v___x_4171_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__16;
                    v___x_4172_ = lean_name_eq(v_id_4153_, v___x_4171_);
                    if v___x_4172_ == 0 {
                        v___x_4173_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8;
                        v___x_4174_ = lean_name_eq(v_id_4153_, v___x_4173_);
                        leanh::lean_dec(v_id_4153_);
                        v___y_4156_ = v___y_4169_;
                        v___y_4157_ = v___x_4171_;
                        v___y_4158_ = v___x_4170_;
                        v___y_4159_ = v___x_4174_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_dec(v_id_4153_);
                        v___y_4156_ = v___y_4169_;
                        v___y_4157_ = v___x_4171_;
                        v___y_4158_ = v___x_4170_;
                        v___y_4159_ = v___x_4172_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_id_4153_);
                    leanh::lean_dec(v___x_4151_);
                    v_a_4136_ = v___x_4170_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___boxed(
    mut v_a_4178_: *mut leanh::LeanObject,
    mut v_a_4179_: *mut leanh::LeanObject,
    mut v_a_4180_: *mut leanh::LeanObject,
    mut v_a_4181_: *mut leanh::LeanObject,
    mut v_a_4182_: *mut leanh::LeanObject,
    mut v_a_4183_: *mut leanh::LeanObject,
    mut v_a_4184_: *mut leanh::LeanObject,
    mut v_a_4185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4186_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(
        v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_,
    );
    leanh::lean_dec(v_a_4184_);
    leanh::lean_dec_ref(v_a_4183_);
    leanh::lean_dec(v_a_4182_);
    leanh::lean_dec_ref(v_a_4181_);
    leanh::lean_dec(v_a_4180_);
    leanh::lean_dec_ref(v_a_4179_);
    return v_res_4186_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4190_ = leanh::lean_box(0);
    v___x_4191_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1;
    v___x_4192_ = l_Lean_mkConst(v___x_4191_, v___x_4190_);
    return v___x_4192_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4193_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2,
    );
    v___x_4194_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4194_, 0, v___x_4193_);
    return v___x_4194_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(
    mut v_a_4198_: *mut leanh::LeanObject,
    mut v_a_4199_: *mut leanh::LeanObject,
    mut v_a_4200_: *mut leanh::LeanObject,
    mut v_a_4201_: *mut leanh::LeanObject,
    mut v_a_4202_: *mut leanh::LeanObject,
    mut v_a_4203_: *mut leanh::LeanObject,
    mut v_a_4204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4210_: u8 = 0;
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4221_: u8 = 0;
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4225_: u8 = 0;
    let mut v_unused_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4230_: u8 = 0;
    let mut v___x_4232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4234_: u8 = 0;
    let mut v_n_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_4198_);
                v_n_4235_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_a_4198_,
                    );
                v___x_4236_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5;
                leanh::lean_inc(v_n_4235_);
                v___x_4237_ = l_Lean_Syntax_isOfKind(v_n_4235_, v___x_4236_);
                if v___x_4237_ == 0 {
                    leanh::lean_dec(v_n_4235_);
                    leanh::lean_dec(v_a_4198_);
                    v___x_4238_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                    v_a_4239_ = leanh::lean_ctor_get(v___x_4238_, 0);
                    v_isSharedCheck_4246_ = (!leanh::lean_is_exclusive(v___x_4238_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4241_ = v___x_4238_;
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4239_);
                        leanh::lean_dec(v___x_4238_);
                        v___x_4241_ = leanh::lean_box(0);
                        v_isShared_4242_ = v_isSharedCheck_4246_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_4247_ = l_Lean_TSyntax_getNat(v_n_4235_);
                    leanh::lean_dec(v_n_4235_);
                    v_a_4207_ = v___x_4247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4208_ = lean_st_ref_get(v_a_4204_);
                v_infoState_4209_ = leanh::lean_ctor_get(v___x_4208_, 7);
                leanh::lean_inc_ref(v_infoState_4209_);
                leanh::lean_dec(v___x_4208_);
                v_enabled_4210_ = leanh::lean_ctor_get_uint8(
                    v_infoState_4209_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_4209_);
                leanh::lean_inc(v_a_4207_);
                v___x_4211_ = l_Lean_mkNatLit(v_a_4207_);
                leanh::lean_inc_ref(v___x_4211_);
                v___x_4212_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4212_, 0, v_a_4207_);
                leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
                if v_enabled_4210_ == 0 {
                    leanh::lean_dec_ref(v___x_4211_);
                    leanh::lean_dec(v_a_4198_);
                    v___x_4213_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4213_, 0, v___x_4212_);
                    return v___x_4213_;
                } else {
                    v___x_4214_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3,
                    );
                    v___x_4215_ = leanh::lean_box(0);
                    v___x_4216_ = leanh::lean_box(0);
                    v___x_4217_ = 0;
                    v___x_4218_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_a_4198_,
                        v___x_4211_,
                        v___x_4214_,
                        v___x_4215_,
                        v___x_4216_,
                        v___x_4217_,
                        v___x_4217_,
                        v_a_4199_,
                        v_a_4200_,
                        v_a_4201_,
                        v_a_4202_,
                        v_a_4203_,
                        v_a_4204_,
                    );
                    if leanh::lean_obj_tag(v___x_4218_) == 0 {
                        v_isSharedCheck_4225_ =
                            (!leanh::lean_is_exclusive(v___x_4218_)) as u8;
                        if v_isSharedCheck_4225_ == 0 {
                            v_unused_4226_ = leanh::lean_ctor_get(v___x_4218_, 0);
                            leanh::lean_dec(v_unused_4226_);
                            v___x_4220_ = v___x_4218_;
                            v_isShared_4221_ = v_isSharedCheck_4225_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4218_);
                            v___x_4220_ = leanh::lean_box(0);
                            v_isShared_4221_ = v_isSharedCheck_4225_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_4212_, 2);
                        v_a_4227_ = leanh::lean_ctor_get(v___x_4218_, 0);
                        v_isSharedCheck_4234_ =
                            (!leanh::lean_is_exclusive(v___x_4218_)) as u8;
                        if v_isSharedCheck_4234_ == 0 {
                            v___x_4229_ = v___x_4218_;
                            v_isShared_4230_ = v_isSharedCheck_4234_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4227_);
                            leanh::lean_dec(v___x_4218_);
                            v___x_4229_ = leanh::lean_box(0);
                            v_isShared_4230_ = v_isSharedCheck_4234_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_4221_ == 0 {
                    leanh::lean_ctor_set(v___x_4220_, 0, v___x_4212_);
                    v___x_4223_ = v___x_4220_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4224_, 0, v___x_4212_);
                    v___x_4223_ = v_reuseFailAlloc_4224_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4223_;
            }
            4 => {
                if v_isShared_4230_ == 0 {
                    v___x_4232_ = v___x_4229_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4233_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
                    v___x_4232_ = v_reuseFailAlloc_4233_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4232_;
            }
            6 => {
                if v_isShared_4242_ == 0 {
                    v___x_4244_ = v___x_4241_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4245_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
                    v___x_4244_ = v_reuseFailAlloc_4245_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___boxed(
    mut v_a_4248_: *mut leanh::LeanObject,
    mut v_a_4249_: *mut leanh::LeanObject,
    mut v_a_4250_: *mut leanh::LeanObject,
    mut v_a_4251_: *mut leanh::LeanObject,
    mut v_a_4252_: *mut leanh::LeanObject,
    mut v_a_4253_: *mut leanh::LeanObject,
    mut v_a_4254_: *mut leanh::LeanObject,
    mut v_a_4255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4256_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(
        v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_,
    );
    leanh::lean_dec(v_a_4254_);
    leanh::lean_dec_ref(v_a_4253_);
    leanh::lean_dec(v_a_4252_);
    leanh::lean_dec_ref(v_a_4251_);
    leanh::lean_dec(v_a_4250_);
    leanh::lean_dec_ref(v_a_4249_);
    return v_res_4256_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Elab_ConfigEval_EvalTerm_evalIntStx_spec__0(
    mut v_a_4257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4258_ = lean_nat_to_int(v_a_4257_);
    return v___x_4258_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = leanh::lean_box(0);
    v___x_4263_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1;
    v___x_4264_ = l_Lean_Expr_const___override(v___x_4263_, v___x_4262_);
    return v___x_4264_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4265_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2,
    );
    v___x_4266_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4266_, 0, v___x_4265_);
    return v___x_4266_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4267_ = leanh::lean_unsigned_to_nat(0);
    v___x_4268_ = lean_nat_to_int(v___x_4267_);
    return v___x_4268_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4274_ = leanh::lean_unsigned_to_nat(0);
    v___x_4275_ = l_Lean_Level_ofNat(v___x_4274_);
    return v___x_4275_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4276_ = leanh::lean_box(0);
    v___x_4277_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8,
    );
    v___x_4278_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4278_, 0, v___x_4277_);
    leanh::lean_ctor_set(v___x_4278_, 1, v___x_4276_);
    return v___x_4278_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4279_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_4280_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__7;
    v___x_4281_ = l_Lean_Expr_const___override(v___x_4280_, v___x_4279_);
    return v___x_4281_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = leanh::lean_box(0);
    v___x_4287_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__12;
    v___x_4288_ = l_Lean_Expr_const___override(v___x_4287_, v___x_4286_);
    return v___x_4288_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(
    mut v_a_4292_: *mut leanh::LeanObject,
    mut v_a_4293_: *mut leanh::LeanObject,
    mut v_a_4294_: *mut leanh::LeanObject,
    mut v_a_4295_: *mut leanh::LeanObject,
    mut v_a_4296_: *mut leanh::LeanObject,
    mut v_a_4297_: *mut leanh::LeanObject,
    mut v_a_4298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4306_: u8 = 0;
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: u8 = 0;
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_unused_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut v_a_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: u8 = 0;
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4347_: u8 = 0;
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4351_: u8 = 0;
    let mut v_n_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4300_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2,
                );
                leanh::lean_inc(v_a_4292_);
                v_n_4352_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_a_4292_,
                    );
                v___x_4353_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__5;
                leanh::lean_inc(v_n_4352_);
                v___x_4354_ = l_Lean_Syntax_isOfKind(v_n_4352_, v___x_4353_);
                if v___x_4354_ == 0 {
                    v___x_4355_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__15;
                    leanh::lean_inc(v_n_4352_);
                    v___x_4356_ = l_Lean_Syntax_isOfKind(v_n_4352_, v___x_4355_);
                    if v___x_4356_ == 0 {
                        leanh::lean_dec(v_n_4352_);
                        leanh::lean_dec(v_a_4292_);
                        v___x_4357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                        v___y_4343_ = v___x_4357_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4358_ = leanh::lean_unsigned_to_nat(1);
                        v_n_4359_ = l_Lean_Syntax_getArg(v_n_4352_, v___x_4358_);
                        leanh::lean_dec(v_n_4352_);
                        leanh::lean_inc(v_n_4359_);
                        v___x_4360_ = l_Lean_Syntax_isOfKind(v_n_4359_, v___x_4353_);
                        if v___x_4360_ == 0 {
                            leanh::lean_dec(v_n_4359_);
                            leanh::lean_dec(v_a_4292_);
                            v___x_4361_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                            v___y_4343_ = v___x_4361_;
                            state = 7;
                            continue;
                        } else {
                            v___x_4362_ = l_Lean_TSyntax_getNat(v_n_4359_);
                            leanh::lean_dec(v_n_4359_);
                            v___x_4363_ = lean_nat_to_int(v___x_4362_);
                            v___x_4364_ = lean_int_neg(v___x_4363_);
                            leanh::lean_dec(v___x_4363_);
                            v_a_4331_ = v___x_4364_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_4365_ = l_Lean_TSyntax_getNat(v_n_4352_);
                    leanh::lean_dec(v_n_4352_);
                    v___x_4366_ = lean_nat_to_int(v___x_4365_);
                    v_a_4331_ = v___x_4366_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                v___x_4304_ = lean_st_ref_get(v_a_4298_);
                v_infoState_4305_ = leanh::lean_ctor_get(v___x_4304_, 7);
                leanh::lean_inc_ref(v_infoState_4305_);
                leanh::lean_dec(v___x_4304_);
                v_enabled_4306_ = leanh::lean_ctor_get_uint8(
                    v_infoState_4305_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_4305_);
                leanh::lean_inc_ref(v___y_4303_);
                v___x_4307_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4307_, 0, v___y_4302_);
                leanh::lean_ctor_set(v___x_4307_, 1, v___y_4303_);
                if v_enabled_4306_ == 0 {
                    leanh::lean_dec_ref(v___y_4303_);
                    leanh::lean_dec(v_a_4292_);
                    v___x_4308_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4308_, 0, v___x_4307_);
                    return v___x_4308_;
                } else {
                    v___x_4309_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3,
                    );
                    v___x_4310_ = leanh::lean_box(0);
                    v___x_4311_ = leanh::lean_box(0);
                    v___x_4312_ = 0;
                    v___x_4313_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_a_4292_,
                        v___y_4303_,
                        v___x_4309_,
                        v___x_4310_,
                        v___x_4311_,
                        v___x_4312_,
                        v___x_4312_,
                        v_a_4293_,
                        v_a_4294_,
                        v_a_4295_,
                        v_a_4296_,
                        v_a_4297_,
                        v_a_4298_,
                    );
                    if leanh::lean_obj_tag(v___x_4313_) == 0 {
                        v_isSharedCheck_4320_ =
                            (!leanh::lean_is_exclusive(v___x_4313_)) as u8;
                        if v_isSharedCheck_4320_ == 0 {
                            v_unused_4321_ = leanh::lean_ctor_get(v___x_4313_, 0);
                            leanh::lean_dec(v_unused_4321_);
                            v___x_4315_ = v___x_4313_;
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4313_);
                            v___x_4315_ = leanh::lean_box(0);
                            v_isShared_4316_ = v_isSharedCheck_4320_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_4307_, 2);
                        v_a_4322_ = leanh::lean_ctor_get(v___x_4313_, 0);
                        v_isSharedCheck_4329_ =
                            (!leanh::lean_is_exclusive(v___x_4313_)) as u8;
                        if v_isSharedCheck_4329_ == 0 {
                            v___x_4324_ = v___x_4313_;
                            v_isShared_4325_ = v_isSharedCheck_4329_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4322_);
                            leanh::lean_dec(v___x_4313_);
                            v___x_4324_ = leanh::lean_box(0);
                            v_isShared_4325_ = v_isSharedCheck_4329_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_4316_ == 0 {
                    leanh::lean_ctor_set(v___x_4315_, 0, v___x_4307_);
                    v___x_4318_ = v___x_4315_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4307_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4318_;
            }
            4 => {
                if v_isShared_4325_ == 0 {
                    v___x_4327_ = v___x_4324_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
                    v___x_4327_ = v_reuseFailAlloc_4328_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4327_;
            }
            6 => {
                v___x_4332_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__4,
                );
                v___x_4333_ = lean_int_dec_le(v___x_4332_, v_a_4331_);
                if v___x_4333_ == 0 {
                    v___x_4334_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__10,
                    );
                    v___x_4335_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__13,
                    );
                    v___x_4336_ = lean_int_neg(v_a_4331_);
                    v___x_4337_ = l_Int_toNat(v___x_4336_);
                    leanh::lean_dec(v___x_4336_);
                    v___x_4338_ = l_Lean_instToExprInt_mkNat(v___x_4337_);
                    v___x_4339_ = l_Lean_mkApp3(v___x_4334_, v___x_4300_, v___x_4335_, v___x_4338_);
                    v___y_4302_ = v_a_4331_;
                    v___y_4303_ = v___x_4339_;
                    state = 1;
                    continue;
                } else {
                    v___x_4340_ = l_Int_toNat(v_a_4331_);
                    v___x_4341_ = l_Lean_instToExprInt_mkNat(v___x_4340_);
                    v___y_4302_ = v_a_4331_;
                    v___y_4303_ = v___x_4341_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v_a_4344_ = leanh::lean_ctor_get(v___y_4343_, 0);
                v_isSharedCheck_4351_ = (!leanh::lean_is_exclusive(v___y_4343_)) as u8;
                if v_isSharedCheck_4351_ == 0 {
                    v___x_4346_ = v___y_4343_;
                    v_isShared_4347_ = v_isSharedCheck_4351_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4344_);
                    leanh::lean_dec(v___y_4343_);
                    v___x_4346_ = leanh::lean_box(0);
                    v_isShared_4347_ = v_isSharedCheck_4351_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_4347_ == 0 {
                    v___x_4349_ = v___x_4346_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4350_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
                    v___x_4349_ = v_reuseFailAlloc_4350_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___boxed(
    mut v_a_4367_: *mut leanh::LeanObject,
    mut v_a_4368_: *mut leanh::LeanObject,
    mut v_a_4369_: *mut leanh::LeanObject,
    mut v_a_4370_: *mut leanh::LeanObject,
    mut v_a_4371_: *mut leanh::LeanObject,
    mut v_a_4372_: *mut leanh::LeanObject,
    mut v_a_4373_: *mut leanh::LeanObject,
    mut v_a_4374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4375_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(
        v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_,
    );
    leanh::lean_dec(v_a_4373_);
    leanh::lean_dec_ref(v_a_4372_);
    leanh::lean_dec(v_a_4371_);
    leanh::lean_dec_ref(v_a_4370_);
    leanh::lean_dec(v_a_4369_);
    leanh::lean_dec_ref(v_a_4368_);
    return v_res_4375_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4379_ = leanh::lean_box(0);
    v___x_4380_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1;
    v___x_4381_ = l_Lean_mkConst(v___x_4380_, v___x_4379_);
    return v___x_4381_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2,
    );
    v___x_4383_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4383_, 0, v___x_4382_);
    return v___x_4383_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(
    mut v_a_4387_: *mut leanh::LeanObject,
    mut v_a_4388_: *mut leanh::LeanObject,
    mut v_a_4389_: *mut leanh::LeanObject,
    mut v_a_4390_: *mut leanh::LeanObject,
    mut v_a_4391_: *mut leanh::LeanObject,
    mut v_a_4392_: *mut leanh::LeanObject,
    mut v_a_4393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_4399_: u8 = 0;
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: u8 = 0;
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_unused_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4419_: u8 = 0;
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut v_s_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: u8 = 0;
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4431_: u8 = 0;
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut v___x_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_4387_);
                v_s_4424_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_a_4387_,
                    );
                v___x_4425_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__5;
                leanh::lean_inc(v_s_4424_);
                v___x_4426_ = l_Lean_Syntax_isOfKind(v_s_4424_, v___x_4425_);
                if v___x_4426_ == 0 {
                    leanh::lean_dec(v_s_4424_);
                    leanh::lean_dec(v_a_4387_);
                    v___x_4427_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                    v_a_4428_ = leanh::lean_ctor_get(v___x_4427_, 0);
                    v_isSharedCheck_4435_ = (!leanh::lean_is_exclusive(v___x_4427_)) as u8;
                    if v_isSharedCheck_4435_ == 0 {
                        v___x_4430_ = v___x_4427_;
                        v_isShared_4431_ = v_isSharedCheck_4435_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4428_);
                        leanh::lean_dec(v___x_4427_);
                        v___x_4430_ = leanh::lean_box(0);
                        v_isShared_4431_ = v_isSharedCheck_4435_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_4436_ = l_Lean_TSyntax_getString(v_s_4424_);
                    leanh::lean_dec(v_s_4424_);
                    v_a_4396_ = v___x_4436_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4397_ = lean_st_ref_get(v_a_4393_);
                v_infoState_4398_ = leanh::lean_ctor_get(v___x_4397_, 7);
                leanh::lean_inc_ref(v_infoState_4398_);
                leanh::lean_dec(v___x_4397_);
                v_enabled_4399_ = leanh::lean_ctor_get_uint8(
                    v_infoState_4398_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_4398_);
                leanh::lean_inc_ref(v_a_4396_);
                v___x_4400_ = l_Lean_mkStrLit(v_a_4396_);
                leanh::lean_inc_ref(v___x_4400_);
                v___x_4401_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4401_, 0, v_a_4396_);
                leanh::lean_ctor_set(v___x_4401_, 1, v___x_4400_);
                if v_enabled_4399_ == 0 {
                    leanh::lean_dec_ref(v___x_4400_);
                    leanh::lean_dec(v_a_4387_);
                    v___x_4402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4402_, 0, v___x_4401_);
                    return v___x_4402_;
                } else {
                    v___x_4403_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3,
                    );
                    v___x_4404_ = leanh::lean_box(0);
                    v___x_4405_ = leanh::lean_box(0);
                    v___x_4406_ = 0;
                    v___x_4407_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_a_4387_,
                        v___x_4400_,
                        v___x_4403_,
                        v___x_4404_,
                        v___x_4405_,
                        v___x_4406_,
                        v___x_4406_,
                        v_a_4388_,
                        v_a_4389_,
                        v_a_4390_,
                        v_a_4391_,
                        v_a_4392_,
                        v_a_4393_,
                    );
                    if leanh::lean_obj_tag(v___x_4407_) == 0 {
                        v_isSharedCheck_4414_ =
                            (!leanh::lean_is_exclusive(v___x_4407_)) as u8;
                        if v_isSharedCheck_4414_ == 0 {
                            v_unused_4415_ = leanh::lean_ctor_get(v___x_4407_, 0);
                            leanh::lean_dec(v_unused_4415_);
                            v___x_4409_ = v___x_4407_;
                            v_isShared_4410_ = v_isSharedCheck_4414_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4407_);
                            v___x_4409_ = leanh::lean_box(0);
                            v_isShared_4410_ = v_isSharedCheck_4414_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_4401_, 2);
                        v_a_4416_ = leanh::lean_ctor_get(v___x_4407_, 0);
                        v_isSharedCheck_4423_ =
                            (!leanh::lean_is_exclusive(v___x_4407_)) as u8;
                        if v_isSharedCheck_4423_ == 0 {
                            v___x_4418_ = v___x_4407_;
                            v_isShared_4419_ = v_isSharedCheck_4423_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4416_);
                            leanh::lean_dec(v___x_4407_);
                            v___x_4418_ = leanh::lean_box(0);
                            v_isShared_4419_ = v_isSharedCheck_4423_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_4410_ == 0 {
                    leanh::lean_ctor_set(v___x_4409_, 0, v___x_4401_);
                    v___x_4412_ = v___x_4409_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4401_);
                    v___x_4412_ = v_reuseFailAlloc_4413_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4412_;
            }
            4 => {
                if v_isShared_4419_ == 0 {
                    v___x_4421_ = v___x_4418_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4422_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
                    v___x_4421_ = v_reuseFailAlloc_4422_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4421_;
            }
            6 => {
                if v_isShared_4431_ == 0 {
                    v___x_4433_ = v___x_4430_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
                    v___x_4433_ = v_reuseFailAlloc_4434_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4433_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___boxed(
    mut v_a_4437_: *mut leanh::LeanObject,
    mut v_a_4438_: *mut leanh::LeanObject,
    mut v_a_4439_: *mut leanh::LeanObject,
    mut v_a_4440_: *mut leanh::LeanObject,
    mut v_a_4441_: *mut leanh::LeanObject,
    mut v_a_4442_: *mut leanh::LeanObject,
    mut v_a_4443_: *mut leanh::LeanObject,
    mut v_a_4444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4445_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(
        v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_,
    );
    leanh::lean_dec(v_a_4443_);
    leanh::lean_dec_ref(v_a_4442_);
    leanh::lean_dec(v_a_4441_);
    leanh::lean_dec_ref(v_a_4440_);
    leanh::lean_dec(v_a_4439_);
    leanh::lean_dec_ref(v_a_4438_);
    return v_res_4445_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(
    mut v_keys_4446_: *mut leanh::LeanObject,
    mut v_i_4447_: *mut leanh::LeanObject,
    mut v_k_4448_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: u8 = 0;
    let mut v_k_x27_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: u8 = 0;
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4449_ = lean_array_get_size(v_keys_4446_);
                v___x_4450_ = lean_nat_dec_lt(v_i_4447_, v___x_4449_);
                if v___x_4450_ == 0 {
                    leanh::lean_dec(v_i_4447_);
                    return v___x_4450_;
                } else {
                    v_k_x27_4451_ = lean_array_fget_borrowed(v_keys_4446_, v_i_4447_);
                    v___x_4452_ = l_Lean_instBEqExtraModUse_beq(v_k_4448_, v_k_x27_4451_);
                    if v___x_4452_ == 0 {
                        v___x_4453_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4454_ = lean_nat_add(v_i_4447_, v___x_4453_);
                        leanh::lean_dec(v_i_4447_);
                        v_i_4447_ = v___x_4454_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_4447_);
                        return v___x_4452_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg___boxed(
    mut v_keys_4456_: *mut leanh::LeanObject,
    mut v_i_4457_: *mut leanh::LeanObject,
    mut v_k_4458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4459_: u8 = 0;
    let mut v_r_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4459_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_keys_4456_, v_i_4457_, v_k_4458_);
    leanh::lean_dec_ref(v_k_4458_);
    leanh::lean_dec_ref(v_keys_4456_);
    v_r_4460_ = leanh::lean_box((v_res_4459_) as usize);
    return v_r_4460_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_4461_: usize = 0;
    let mut v___x_4462_: usize = 0;
    let mut v___x_4463_: usize = 0;
    v___x_4461_ = 5usize;
    v___x_4462_ = 1usize;
    v___x_4463_ = lean_usize_shift_left(v___x_4462_, v___x_4461_);
    return v___x_4463_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_4464_: usize = 0;
    let mut v___x_4465_: usize = 0;
    let mut v___x_4466_: usize = 0;
    v___x_4464_ = 1usize;
    v___x_4465_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
    v___x_4466_ = lean_usize_sub(v___x_4465_, v___x_4464_);
    return v___x_4466_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_x_4467_: *mut leanh::LeanObject,
    mut v_x_4468_: usize,
    mut v_x_4469_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: usize = 0;
    let mut v___x_4473_: usize = 0;
    let mut v___x_4474_: usize = 0;
    let mut v_j_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: u8 = 0;
    let mut v_node_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: usize = 0;
    let mut v___x_4482_: u8 = 0;
    let mut v_ks_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4467_) == 0 {
                    v_es_4470_ = leanh::lean_ctor_get(v_x_4467_, 0);
                    v___x_4471_ = leanh::lean_box(2);
                    v___x_4472_ = 5usize;
                    v___x_4473_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
                    v___x_4474_ = lean_usize_land(v_x_4468_, v___x_4473_);
                    v_j_4475_ = lean_usize_to_nat(v___x_4474_);
                    v___x_4476_ = lean_array_get_borrowed(v___x_4471_, v_es_4470_, v_j_4475_);
                    leanh::lean_dec(v_j_4475_);
                    match leanh::lean_obj_tag(v___x_4476_) {
                        0 => {
                            v_key_4477_ = leanh::lean_ctor_get(v___x_4476_, 0);
                            v___x_4478_ = l_Lean_instBEqExtraModUse_beq(v_x_4469_, v_key_4477_);
                            return v___x_4478_;
                        }
                        1 => {
                            v_node_4479_ = leanh::lean_ctor_get(v___x_4476_, 0);
                            v___x_4480_ = lean_usize_shift_right(v_x_4468_, v___x_4472_);
                            v_x_4467_ = v_node_4479_;
                            v_x_4468_ = v___x_4480_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4482_ = 0;
                            return v___x_4482_;
                        }
                    }
                } else {
                    v_ks_4483_ = leanh::lean_ctor_get(v_x_4467_, 0);
                    v___x_4484_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4485_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_ks_4483_, v___x_4484_, v_x_4469_);
                    return v___x_4485_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_x_4486_: *mut leanh::LeanObject,
    mut v_x_4487_: *mut leanh::LeanObject,
    mut v_x_4488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_10220__boxed_4489_: usize = 0;
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_10220__boxed_4489_ = leanh::lean_unbox_usize(v_x_4487_);
    leanh::lean_dec(v_x_4487_);
    v_res_4490_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4486_, v_x_10220__boxed_4489_, v_x_4488_);
    leanh::lean_dec_ref(v_x_4488_);
    leanh::lean_dec_ref(v_x_4486_);
    v_r_4491_ = leanh::lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(
    mut v_x_4492_: *mut leanh::LeanObject,
    mut v_x_4493_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4494_: u64 = 0;
    let mut v___x_4495_: usize = 0;
    let mut v___x_4496_: u8 = 0;
    v___x_4494_ = l_Lean_instHashableExtraModUse_hash(v_x_4493_);
    v___x_4495_ = lean_uint64_to_usize(v___x_4494_);
    v___x_4496_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_4492_, v___x_4495_, v_x_4493_);
    return v___x_4496_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4497_: *mut leanh::LeanObject,
    mut v_x_4498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4499_: u8 = 0;
    let mut v_r_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4499_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_4497_, v_x_4498_);
    leanh::lean_dec_ref(v_x_4498_);
    leanh::lean_dec_ref(v_x_4497_);
    v_r_4500_ = leanh::lean_box((v_res_4499_) as usize);
    return v_r_4500_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(
    mut v_msgData_4501_: *mut leanh::LeanObject,
    mut v___y_4502_: *mut leanh::LeanObject,
    mut v___y_4503_: *mut leanh::LeanObject,
    mut v___y_4504_: *mut leanh::LeanObject,
    mut v___y_4505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4507_ = lean_st_ref_get(v___y_4505_);
    v_env_4508_ = leanh::lean_ctor_get(v___x_4507_, 0);
    leanh::lean_inc_ref(v_env_4508_);
    leanh::lean_dec(v___x_4507_);
    v___x_4509_ = lean_st_ref_get(v___y_4503_);
    v_mctx_4510_ = leanh::lean_ctor_get(v___x_4509_, 0);
    leanh::lean_inc_ref(v_mctx_4510_);
    leanh::lean_dec(v___x_4509_);
    v_lctx_4511_ = leanh::lean_ctor_get(v___y_4502_, 2);
    v_options_4512_ = leanh::lean_ctor_get(v___y_4504_, 2);
    leanh::lean_inc_ref(v_options_4512_);
    leanh::lean_inc_ref(v_lctx_4511_);
    v___x_4513_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4513_, 0, v_env_4508_);
    leanh::lean_ctor_set(v___x_4513_, 1, v_mctx_4510_);
    leanh::lean_ctor_set(v___x_4513_, 2, v_lctx_4511_);
    leanh::lean_ctor_set(v___x_4513_, 3, v_options_4512_);
    v___x_4514_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4514_, 0, v___x_4513_);
    leanh::lean_ctor_set(v___x_4514_, 1, v_msgData_4501_);
    v___x_4515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4515_, 0, v___x_4514_);
    return v___x_4515_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_msgData_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
    mut v___y_4519_: *mut leanh::LeanObject,
    mut v___y_4520_: *mut leanh::LeanObject,
    mut v___y_4521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4522_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msgData_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
    leanh::lean_dec(v___y_4520_);
    leanh::lean_dec_ref(v___y_4519_);
    leanh::lean_dec(v___y_4518_);
    leanh::lean_dec_ref(v___y_4517_);
    return v_res_4522_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0()
-> f64 {
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: f64 = 0.0;
    v___x_4523_ = leanh::lean_unsigned_to_nat(0);
    v___x_4524_ = lean_float_of_nat(v___x_4523_);
    return v___x_4524_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(
    mut v_cls_4528_: *mut leanh::LeanObject,
    mut v_msg_4529_: *mut leanh::LeanObject,
    mut v___y_4530_: *mut leanh::LeanObject,
    mut v___y_4531_: *mut leanh::LeanObject,
    mut v___y_4532_: *mut leanh::LeanObject,
    mut v___y_4533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4540_: u8 = 0;
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4553_: u8 = 0;
    let mut v_tid_4554_: u64 = 0;
    let mut v_traces_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4558_: u8 = 0;
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: f64 = 0.0;
    let mut v___x_4561_: u8 = 0;
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4579_: u8 = 0;
    let mut v_isSharedCheck_4580_: u8 = 0;
    let mut v_isSharedCheck_4581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4535_ = leanh::lean_ctor_get(v___y_4532_, 5);
                v___x_4536_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
                v_a_4537_ = leanh::lean_ctor_get(v___x_4536_, 0);
                v_isSharedCheck_4581_ = (!leanh::lean_is_exclusive(v___x_4536_)) as u8;
                if v_isSharedCheck_4581_ == 0 {
                    v___x_4539_ = v___x_4536_;
                    v_isShared_4540_ = v_isSharedCheck_4581_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4537_);
                    leanh::lean_dec(v___x_4536_);
                    v___x_4539_ = leanh::lean_box(0);
                    v_isShared_4540_ = v_isSharedCheck_4581_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4541_ = lean_st_ref_take(v___y_4533_);
                v_traceState_4542_ = leanh::lean_ctor_get(v___x_4541_, 4);
                v_env_4543_ = leanh::lean_ctor_get(v___x_4541_, 0);
                v_nextMacroScope_4544_ = leanh::lean_ctor_get(v___x_4541_, 1);
                v_ngen_4545_ = leanh::lean_ctor_get(v___x_4541_, 2);
                v_auxDeclNGen_4546_ = leanh::lean_ctor_get(v___x_4541_, 3);
                v_cache_4547_ = leanh::lean_ctor_get(v___x_4541_, 5);
                v_messages_4548_ = leanh::lean_ctor_get(v___x_4541_, 6);
                v_infoState_4549_ = leanh::lean_ctor_get(v___x_4541_, 7);
                v_snapshotTasks_4550_ = leanh::lean_ctor_get(v___x_4541_, 8);
                v_isSharedCheck_4580_ = (!leanh::lean_is_exclusive(v___x_4541_)) as u8;
                if v_isSharedCheck_4580_ == 0 {
                    v___x_4552_ = v___x_4541_;
                    v_isShared_4553_ = v_isSharedCheck_4580_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4550_);
                    leanh::lean_inc(v_infoState_4549_);
                    leanh::lean_inc(v_messages_4548_);
                    leanh::lean_inc(v_cache_4547_);
                    leanh::lean_inc(v_traceState_4542_);
                    leanh::lean_inc(v_auxDeclNGen_4546_);
                    leanh::lean_inc(v_ngen_4545_);
                    leanh::lean_inc(v_nextMacroScope_4544_);
                    leanh::lean_inc(v_env_4543_);
                    leanh::lean_dec(v___x_4541_);
                    v___x_4552_ = leanh::lean_box(0);
                    v_isShared_4553_ = v_isSharedCheck_4580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4554_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4542_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4555_ = leanh::lean_ctor_get(v_traceState_4542_, 0);
                v_isSharedCheck_4579_ =
                    (!leanh::lean_is_exclusive(v_traceState_4542_)) as u8;
                if v_isSharedCheck_4579_ == 0 {
                    v___x_4557_ = v_traceState_4542_;
                    v_isShared_4558_ = v_isSharedCheck_4579_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4555_);
                    leanh::lean_dec(v_traceState_4542_);
                    v___x_4557_ = leanh::lean_box(0);
                    v_isShared_4558_ = v_isSharedCheck_4579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4559_ = leanh::lean_box(0);
                v___x_4560_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__0);
                v___x_4561_ = 0;
                v___x_4562_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1;
                v___x_4563_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4563_, 0, v_cls_4528_);
                leanh::lean_ctor_set(v___x_4563_, 1, v___x_4559_);
                leanh::lean_ctor_set(v___x_4563_, 2, v___x_4562_);
                leanh::lean_ctor_set_float(
                    v___x_4563_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4560_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4563_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4560_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4563_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4561_,
                );
                v___x_4564_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__2;
                v___x_4565_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4565_, 0, v___x_4563_);
                leanh::lean_ctor_set(v___x_4565_, 1, v_a_4537_);
                leanh::lean_ctor_set(v___x_4565_, 2, v___x_4564_);
                leanh::lean_inc(v_ref_4535_);
                v___x_4566_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4566_, 0, v_ref_4535_);
                leanh::lean_ctor_set(v___x_4566_, 1, v___x_4565_);
                v___x_4567_ = l_Lean_PersistentArray_push___redArg(v_traces_4555_, v___x_4566_);
                if v_isShared_4558_ == 0 {
                    leanh::lean_ctor_set(v___x_4557_, 0, v___x_4567_);
                    v___x_4569_ = v___x_4557_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4578_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4567_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4578_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4554_,
                    );
                    v___x_4569_ = v_reuseFailAlloc_4578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4553_ == 0 {
                    leanh::lean_ctor_set(v___x_4552_, 4, v___x_4569_);
                    v___x_4571_ = v___x_4552_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_env_4543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 1, v_nextMacroScope_4544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 2, v_ngen_4545_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 3, v_auxDeclNGen_4546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 4, v___x_4569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 5, v_cache_4547_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 6, v_messages_4548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 7, v_infoState_4549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4577_, 8, v_snapshotTasks_4550_);
                    v___x_4571_ = v_reuseFailAlloc_4577_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4572_ = lean_st_ref_set(v___y_4533_, v___x_4571_);
                v___x_4573_ = leanh::lean_box(0);
                if v_isShared_4540_ == 0 {
                    leanh::lean_ctor_set(v___x_4539_, 0, v___x_4573_);
                    v___x_4575_ = v___x_4539_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4576_, 0, v___x_4573_);
                    v___x_4575_ = v_reuseFailAlloc_4576_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_cls_4582_: *mut leanh::LeanObject,
    mut v_msg_4583_: *mut leanh::LeanObject,
    mut v___y_4584_: *mut leanh::LeanObject,
    mut v___y_4585_: *mut leanh::LeanObject,
    mut v___y_4586_: *mut leanh::LeanObject,
    mut v___y_4587_: *mut leanh::LeanObject,
    mut v___y_4588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4589_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_4582_, v_msg_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
    leanh::lean_dec(v___y_4587_);
    leanh::lean_dec_ref(v___y_4586_);
    leanh::lean_dec(v___y_4585_);
    leanh::lean_dec_ref(v___y_4584_);
    return v_res_4589_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4592_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__1;
    v___x_4593_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__0;
    v___x_4594_ = l_Lean_PersistentHashMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4593_,
        v___x_4592_,
    );
    return v___x_4594_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4595_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4595_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__3);
    v___x_4597_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4597_, 0, v___x_4596_);
    return v___x_4597_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4598_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
    v___x_4599_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4599_, 0, v___x_4598_);
    leanh::lean_ctor_set(v___x_4599_, 1, v___x_4598_);
    return v___x_4599_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4600_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__4);
    v___x_4601_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_4601_, 0, v___x_4600_);
    leanh::lean_ctor_set(v___x_4601_, 1, v___x_4600_);
    leanh::lean_ctor_set(v___x_4601_, 2, v___x_4600_);
    leanh::lean_ctor_set(v___x_4601_, 3, v___x_4600_);
    leanh::lean_ctor_set(v___x_4601_, 4, v___x_4600_);
    leanh::lean_ctor_set(v___x_4601_, 5, v___x_4600_);
    return v___x_4601_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4606_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__9;
    v___x_4607_ = l_Lean_stringToMessageData(v___x_4606_);
    return v___x_4607_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__11;
    v___x_4610_ = l_Lean_stringToMessageData(v___x_4609_);
    return v___x_4610_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4611_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg___closed__1;
    v___x_4612_ = l_Lean_stringToMessageData(v___x_4611_);
    return v___x_4612_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16()
-> *mut leanh::LeanObject {
    let mut v_cls_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_4616_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8;
    v___x_4617_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__15;
    v___x_4618_ = l_Lean_Name_append(v___x_4617_, v_cls_4616_);
    return v___x_4618_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__17;
    v___x_4621_ = l_Lean_stringToMessageData(v___x_4620_);
    return v___x_4621_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4623_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__19;
    v___x_4624_ = l_Lean_stringToMessageData(v___x_4623_);
    return v___x_4624_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(
    mut v_mod_4629_: *mut leanh::LeanObject,
    mut v_isMeta_4630_: u8,
    mut v_hint_4631_: *mut leanh::LeanObject,
    mut v___y_4632_: *mut leanh::LeanObject,
    mut v___y_4633_: *mut leanh::LeanObject,
    mut v___y_4634_: *mut leanh::LeanObject,
    mut v___y_4635_: *mut leanh::LeanObject,
    mut v___y_4636_: *mut leanh::LeanObject,
    mut v___y_4637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4641_: u8 = 0;
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4664_: u8 = 0;
    let mut v_asyncMode_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4678_: u8 = 0;
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4686_: u8 = 0;
    let mut v_unused_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_unused_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: u8 = 0;
    let mut v_options_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4694_: u8 = 0;
    let mut v_inheritedTraceOptions_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: u8 = 0;
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: u8 = 0;
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4639_ = lean_st_ref_get(v___y_4637_);
                v_env_4640_ = leanh::lean_ctor_get(v___x_4639_, 0);
                leanh::lean_inc_ref(v_env_4640_);
                leanh::lean_dec(v___x_4639_);
                v_isExporting_4641_ = leanh::lean_ctor_get_uint8(
                    v_env_4640_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_4640_);
                v___x_4642_ = lean_st_ref_get(v___y_4637_);
                v_env_4643_ = leanh::lean_ctor_get(v___x_4642_, 0);
                leanh::lean_inc_ref(v_env_4643_);
                leanh::lean_dec(v___x_4642_);
                v___x_4644_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__2);
                leanh::lean_inc(v_mod_4629_);
                v_entry_4645_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                leanh::lean_ctor_set(v_entry_4645_, 0, v_mod_4629_);
                leanh::lean_ctor_set_uint8(
                    v_entry_4645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isExporting_4641_,
                );
                leanh::lean_ctor_set_uint8(
                    v_entry_4645_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4630_,
                );
                v___x_4646_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4647_ = leanh::lean_box(1);
                v___x_4648_ = leanh::lean_box(0);
                v___x_4691_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4644_,
                    v___x_4646_,
                    v_env_4643_,
                    v___x_4647_,
                    v___x_4648_,
                );
                v___x_4692_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v___x_4691_, v_entry_4645_);
                leanh::lean_dec(v___x_4691_);
                if v___x_4692_ == 0 {
                    v_options_4693_ = leanh::lean_ctor_get(v___y_4636_, 2);
                    v_hasTrace_4694_ = leanh::lean_ctor_get_uint8(
                        v_options_4693_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4694_ == 0 {
                        leanh::lean_dec(v_hint_4631_);
                        leanh::lean_dec(v_mod_4629_);
                        v___y_4650_ = v___y_4635_;
                        v___y_4651_ = v___y_4637_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4695_ =
                            leanh::lean_ctor_get(v___y_4636_, 13);
                        v_cls_4696_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__8;
                        v___x_4716_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__16);
                        v___x_4717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4695_,
                            v_options_4693_,
                            v___x_4716_,
                        );
                        if v___x_4717_ == 0 {
                            leanh::lean_dec(v_hint_4631_);
                            leanh::lean_dec(v_mod_4629_);
                            v___y_4650_ = v___y_4635_;
                            v___y_4651_ = v___y_4637_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4718_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__18);
                            if v_isExporting_4641_ == 0 {
                                v___x_4727_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__23;
                                v___y_4720_ = v___x_4727_;
                                state = 8;
                                continue;
                            } else {
                                v___x_4728_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__24;
                                v___y_4720_ = v___x_4728_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_entry_4645_, 1);
                    leanh::lean_dec(v_hint_4631_);
                    leanh::lean_dec(v_mod_4629_);
                    v___x_4729_ = leanh::lean_box(0);
                    v___x_4730_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4730_, 0, v___x_4729_);
                    return v___x_4730_;
                }
            }
            1 => {
                v___x_4652_ = lean_st_ref_take(v___y_4651_);
                v_toEnvExtension_4653_ = leanh::lean_ctor_get(v___x_4646_, 0);
                v_env_4654_ = leanh::lean_ctor_get(v___x_4652_, 0);
                v_nextMacroScope_4655_ = leanh::lean_ctor_get(v___x_4652_, 1);
                v_ngen_4656_ = leanh::lean_ctor_get(v___x_4652_, 2);
                v_auxDeclNGen_4657_ = leanh::lean_ctor_get(v___x_4652_, 3);
                v_traceState_4658_ = leanh::lean_ctor_get(v___x_4652_, 4);
                v_messages_4659_ = leanh::lean_ctor_get(v___x_4652_, 6);
                v_infoState_4660_ = leanh::lean_ctor_get(v___x_4652_, 7);
                v_snapshotTasks_4661_ = leanh::lean_ctor_get(v___x_4652_, 8);
                v_isSharedCheck_4689_ = (!leanh::lean_is_exclusive(v___x_4652_)) as u8;
                if v_isSharedCheck_4689_ == 0 {
                    v_unused_4690_ = leanh::lean_ctor_get(v___x_4652_, 5);
                    leanh::lean_dec(v_unused_4690_);
                    v___x_4663_ = v___x_4652_;
                    v_isShared_4664_ = v_isSharedCheck_4689_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4661_);
                    leanh::lean_inc(v_infoState_4660_);
                    leanh::lean_inc(v_messages_4659_);
                    leanh::lean_inc(v_traceState_4658_);
                    leanh::lean_inc(v_auxDeclNGen_4657_);
                    leanh::lean_inc(v_ngen_4656_);
                    leanh::lean_inc(v_nextMacroScope_4655_);
                    leanh::lean_inc(v_env_4654_);
                    leanh::lean_dec(v___x_4652_);
                    v___x_4663_ = leanh::lean_box(0);
                    v_isShared_4664_ = v_isSharedCheck_4689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4665_ = leanh::lean_ctor_get(v_toEnvExtension_4653_, 2);
                v___x_4666_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4646_,
                    v_env_4654_,
                    v_entry_4645_,
                    v_asyncMode_4665_,
                    v___x_4648_,
                );
                v___x_4667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
                if v_isShared_4664_ == 0 {
                    leanh::lean_ctor_set(v___x_4663_, 5, v___x_4667_);
                    leanh::lean_ctor_set(v___x_4663_, 0, v___x_4666_);
                    v___x_4669_ = v___x_4663_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4688_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 1, v_nextMacroScope_4655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 2, v_ngen_4656_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 3, v_auxDeclNGen_4657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 4, v_traceState_4658_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 5, v___x_4667_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 6, v_messages_4659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 7, v_infoState_4660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 8, v_snapshotTasks_4661_);
                    v___x_4669_ = v_reuseFailAlloc_4688_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4670_ = lean_st_ref_set(v___y_4651_, v___x_4669_);
                v___x_4671_ = lean_st_ref_take(v___y_4650_);
                v_mctx_4672_ = leanh::lean_ctor_get(v___x_4671_, 0);
                v_zetaDeltaFVarIds_4673_ = leanh::lean_ctor_get(v___x_4671_, 2);
                v_postponed_4674_ = leanh::lean_ctor_get(v___x_4671_, 3);
                v_diag_4675_ = leanh::lean_ctor_get(v___x_4671_, 4);
                v_isSharedCheck_4686_ = (!leanh::lean_is_exclusive(v___x_4671_)) as u8;
                if v_isSharedCheck_4686_ == 0 {
                    v_unused_4687_ = leanh::lean_ctor_get(v___x_4671_, 1);
                    leanh::lean_dec(v_unused_4687_);
                    v___x_4677_ = v___x_4671_;
                    v_isShared_4678_ = v_isSharedCheck_4686_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4675_);
                    leanh::lean_inc(v_postponed_4674_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4673_);
                    leanh::lean_inc(v_mctx_4672_);
                    leanh::lean_dec(v___x_4671_);
                    v___x_4677_ = leanh::lean_box(0);
                    v_isShared_4678_ = v_isSharedCheck_4686_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
                if v_isShared_4678_ == 0 {
                    leanh::lean_ctor_set(v___x_4677_, 1, v___x_4679_);
                    v___x_4681_ = v___x_4677_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4685_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_mctx_4672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4679_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4685_,
                        2,
                        v_zetaDeltaFVarIds_4673_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 3, v_postponed_4674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4685_, 4, v_diag_4675_);
                    v___x_4681_ = v_reuseFailAlloc_4685_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4682_ = lean_st_ref_set(v___y_4650_, v___x_4681_);
                v___x_4683_ = leanh::lean_box(0);
                v___x_4684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4684_, 0, v___x_4683_);
                return v___x_4684_;
            }
            6 => {
                v___x_4700_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4700_, 0, v___y_4698_);
                leanh::lean_ctor_set(v___x_4700_, 1, v___y_4699_);
                v___x_4701_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_4696_, v___x_4700_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
                if leanh::lean_obj_tag(v___x_4701_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4701_, 1);
                    v___y_4650_ = v___y_4635_;
                    v___y_4651_ = v___y_4637_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_entry_4645_, 1);
                    return v___x_4701_;
                }
            }
            7 => {
                leanh::lean_inc_ref(v___y_4704_);
                v___x_4705_ = l_Lean_stringToMessageData(v___y_4704_);
                v___x_4706_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4706_, 0, v___y_4703_);
                leanh::lean_ctor_set(v___x_4706_, 1, v___x_4705_);
                v___x_4707_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__10);
                v___x_4708_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4708_, 0, v___x_4706_);
                leanh::lean_ctor_set(v___x_4708_, 1, v___x_4707_);
                v___x_4709_ = l_Lean_MessageData_ofName(v_mod_4629_);
                v___x_4710_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4710_, 0, v___x_4708_);
                leanh::lean_ctor_set(v___x_4710_, 1, v___x_4709_);
                v___x_4711_ = l_Lean_Name_isAnonymous(v_hint_4631_);
                if v___x_4711_ == 0 {
                    v___x_4712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__12);
                    v___x_4713_ = l_Lean_MessageData_ofName(v_hint_4631_);
                    v___x_4714_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4714_, 0, v___x_4712_);
                    leanh::lean_ctor_set(v___x_4714_, 1, v___x_4713_);
                    v___y_4698_ = v___x_4710_;
                    v___y_4699_ = v___x_4714_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_hint_4631_);
                    v___x_4715_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__13);
                    v___y_4698_ = v___x_4710_;
                    v___y_4699_ = v___x_4715_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                leanh::lean_inc_ref(v___y_4720_);
                v___x_4721_ = l_Lean_stringToMessageData(v___y_4720_);
                v___x_4722_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4722_, 0, v___x_4718_);
                leanh::lean_ctor_set(v___x_4722_, 1, v___x_4721_);
                v___x_4723_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__20);
                v___x_4724_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4724_, 0, v___x_4722_);
                leanh::lean_ctor_set(v___x_4724_, 1, v___x_4723_);
                if v_isMeta_4630_ == 0 {
                    v___x_4725_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__21;
                    v___y_4703_ = v___x_4724_;
                    v___y_4704_ = v___x_4725_;
                    state = 7;
                    continue;
                } else {
                    v___x_4726_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__22;
                    v___y_4703_ = v___x_4724_;
                    v___y_4704_ = v___x_4726_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___boxed(
    mut v_mod_4731_: *mut leanh::LeanObject,
    mut v_isMeta_4732_: *mut leanh::LeanObject,
    mut v_hint_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
    mut v___y_4739_: *mut leanh::LeanObject,
    mut v___y_4740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_4741_: u8 = 0;
    let mut v_res_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4741_ = (leanh::lean_unbox(v_isMeta_4732_) as u8);
    v_res_4742_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_mod_4731_, v_isMeta_boxed_4741_, v_hint_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_);
    leanh::lean_dec(v___y_4739_);
    leanh::lean_dec_ref(v___y_4738_);
    leanh::lean_dec(v___y_4737_);
    leanh::lean_dec_ref(v___y_4736_);
    leanh::lean_dec(v___y_4735_);
    leanh::lean_dec_ref(v___y_4734_);
    return v_res_4742_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(
    mut v___x_4743_: *mut leanh::LeanObject,
    mut v_declName_4744_: *mut leanh::LeanObject,
    mut v_as_4745_: *mut leanh::LeanObject,
    mut v_sz_4746_: usize,
    mut v_i_4747_: usize,
    mut v_b_4748_: *mut leanh::LeanObject,
    mut v___y_4749_: *mut leanh::LeanObject,
    mut v___y_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
    mut v___y_4752_: *mut leanh::LeanObject,
    mut v___y_4753_: *mut leanh::LeanObject,
    mut v___y_4754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4756_: u8 = 0;
    let mut v___x_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: u8 = 0;
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: usize = 0;
    let mut v___x_4769_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4756_ = lean_usize_dec_lt(v_i_4747_, v_sz_4746_);
                if v___x_4756_ == 0 {
                    leanh::lean_dec(v_declName_4744_);
                    v___x_4757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4757_, 0, v_b_4748_);
                    return v___x_4757_;
                } else {
                    v___x_4758_ = l_Lean_Environment_header(v___x_4743_);
                    v_modules_4759_ = leanh::lean_ctor_get(v___x_4758_, 3);
                    leanh::lean_inc_ref(v_modules_4759_);
                    leanh::lean_dec_ref(v___x_4758_);
                    v___x_4760_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4761_ = lean_array_uget_borrowed(v_as_4745_, v_i_4747_);
                    v___x_4762_ = lean_array_get(v___x_4760_, v_modules_4759_, v_a_4761_);
                    leanh::lean_dec_ref(v_modules_4759_);
                    v_toImport_4763_ = leanh::lean_ctor_get(v___x_4762_, 0);
                    leanh::lean_inc_ref(v_toImport_4763_);
                    leanh::lean_dec(v___x_4762_);
                    v_module_4764_ = leanh::lean_ctor_get(v_toImport_4763_, 0);
                    leanh::lean_inc(v_module_4764_);
                    leanh::lean_dec_ref(v_toImport_4763_);
                    v___x_4765_ = 0;
                    leanh::lean_inc(v_declName_4744_);
                    v___x_4766_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_4764_, v___x_4765_, v_declName_4744_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_);
                    if leanh::lean_obj_tag(v___x_4766_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4766_, 1);
                        v___x_4767_ = leanh::lean_box(0);
                        v___x_4768_ = 1usize;
                        v___x_4769_ = lean_usize_add(v_i_4747_, v___x_4768_);
                        v_i_4747_ = v___x_4769_;
                        v_b_4748_ = v___x_4767_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_4744_);
                        return v___x_4766_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1___boxed(
    mut v___x_4771_: *mut leanh::LeanObject,
    mut v_declName_4772_: *mut leanh::LeanObject,
    mut v_as_4773_: *mut leanh::LeanObject,
    mut v_sz_4774_: *mut leanh::LeanObject,
    mut v_i_4775_: *mut leanh::LeanObject,
    mut v_b_4776_: *mut leanh::LeanObject,
    mut v___y_4777_: *mut leanh::LeanObject,
    mut v___y_4778_: *mut leanh::LeanObject,
    mut v___y_4779_: *mut leanh::LeanObject,
    mut v___y_4780_: *mut leanh::LeanObject,
    mut v___y_4781_: *mut leanh::LeanObject,
    mut v___y_4782_: *mut leanh::LeanObject,
    mut v___y_4783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4784_: usize = 0;
    let mut v_i_boxed_4785_: usize = 0;
    let mut v_res_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4784_ = leanh::lean_unbox_usize(v_sz_4774_);
    leanh::lean_dec(v_sz_4774_);
    v_i_boxed_4785_ = leanh::lean_unbox_usize(v_i_4775_);
    leanh::lean_dec(v_i_4775_);
    v_res_4786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v___x_4771_, v_declName_4772_, v_as_4773_, v_sz_boxed_4784_, v_i_boxed_4785_, v_b_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
    leanh::lean_dec(v___y_4782_);
    leanh::lean_dec_ref(v___y_4781_);
    leanh::lean_dec(v___y_4780_);
    leanh::lean_dec_ref(v___y_4779_);
    leanh::lean_dec(v___y_4778_);
    leanh::lean_dec_ref(v___y_4777_);
    leanh::lean_dec_ref(v_as_4773_);
    leanh::lean_dec_ref(v___x_4771_);
    return v_res_4786_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(
    mut v_a_4787_: *mut leanh::LeanObject,
    mut v_x_4788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4788_) == 0 {
                    v___x_4789_ = leanh::lean_box(0);
                    return v___x_4789_;
                } else {
                    v_key_4790_ = leanh::lean_ctor_get(v_x_4788_, 0);
                    v_value_4791_ = leanh::lean_ctor_get(v_x_4788_, 1);
                    v_tail_4792_ = leanh::lean_ctor_get(v_x_4788_, 2);
                    v___x_4793_ = lean_name_eq(v_key_4790_, v_a_4787_);
                    if v___x_4793_ == 0 {
                        v_x_4788_ = v_tail_4792_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_4791_);
                        v___x_4795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4795_, 0, v_value_4791_);
                        return v___x_4795_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_a_4796_: *mut leanh::LeanObject,
    mut v_x_4797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_4796_, v_x_4797_);
    leanh::lean_dec(v_x_4797_);
    leanh::lean_dec(v_a_4796_);
    return v_res_4798_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: u64 = 0;
    v___x_4799_ = leanh::lean_unsigned_to_nat(1723);
    v___x_4800_ = lean_uint64_of_nat(v___x_4799_);
    return v___x_4800_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(
    mut v_m_4801_: *mut leanh::LeanObject,
    mut v_a_4802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4806_: u64 = 0;
    let mut v___x_4807_: u64 = 0;
    let mut v___x_4808_: u64 = 0;
    let mut v_fold_4809_: u64 = 0;
    let mut v___x_4810_: u64 = 0;
    let mut v___x_4811_: u64 = 0;
    let mut v___x_4812_: u64 = 0;
    let mut v___x_4813_: usize = 0;
    let mut v___x_4814_: usize = 0;
    let mut v___x_4815_: usize = 0;
    let mut v___x_4816_: usize = 0;
    let mut v___x_4817_: usize = 0;
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u64 = 0;
    let mut v_hash_4821_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4803_ = leanh::lean_ctor_get(v_m_4801_, 1);
                v___x_4804_ = lean_array_get_size(v_buckets_4803_);
                if leanh::lean_obj_tag(v_a_4802_) == 0 {
                    v___x_4820_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___closed__0);
                    v___y_4806_ = v___x_4820_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4821_ = leanh::lean_ctor_get_uint64(
                        v_a_4802_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4806_ = v_hash_4821_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4807_ = 32u64;
                v___x_4808_ = lean_uint64_shift_right(v___y_4806_, v___x_4807_);
                v_fold_4809_ = lean_uint64_xor(v___y_4806_, v___x_4808_);
                v___x_4810_ = 16u64;
                v___x_4811_ = lean_uint64_shift_right(v_fold_4809_, v___x_4810_);
                v___x_4812_ = lean_uint64_xor(v_fold_4809_, v___x_4811_);
                v___x_4813_ = lean_uint64_to_usize(v___x_4812_);
                v___x_4814_ = lean_usize_of_nat(v___x_4804_);
                v___x_4815_ = 1usize;
                v___x_4816_ = lean_usize_sub(v___x_4814_, v___x_4815_);
                v___x_4817_ = lean_usize_land(v___x_4813_, v___x_4816_);
                v___x_4818_ = lean_array_uget_borrowed(v_buckets_4803_, v___x_4817_);
                v___x_4819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_4802_, v___x_4818_);
                return v___x_4819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg___boxed(
    mut v_m_4822_: *mut leanh::LeanObject,
    mut v_a_4823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4824_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_4822_, v_a_4823_);
    leanh::lean_dec(v_a_4823_);
    leanh::lean_dec_ref(v_m_4822_);
    return v_res_4824_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4827_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__1;
    v___x_4828_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__0;
    v___x_4829_ = l_Std_HashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4828_,
        v___x_4827_,
    );
    return v___x_4829_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(
    mut v_declName_4832_: *mut leanh::LeanObject,
    mut v_isMeta_4833_: u8,
    mut v___y_4834_: *mut leanh::LeanObject,
    mut v___y_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
    mut v___y_4837_: *mut leanh::LeanObject,
    mut v___y_4838_: *mut leanh::LeanObject,
    mut v___y_4839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4849_: usize = 0;
    let mut v___x_4850_: usize = 0;
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4854_: u8 = 0;
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4858_: u8 = 0;
    let mut v_unused_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: u8 = 0;
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4871_: u8 = 0;
    let mut v_toImport_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: u8 = 0;
    let mut v___x_4883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4841_ = lean_st_ref_get(v___y_4839_);
                v_env_4845_ = leanh::lean_ctor_get(v___x_4841_, 0);
                leanh::lean_inc_ref(v_env_4845_);
                leanh::lean_dec(v___x_4841_);
                v___x_4860_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4845_, v_declName_4832_);
                if leanh::lean_obj_tag(v___x_4860_) == 0 {
                    leanh::lean_dec_ref(v_env_4845_);
                    leanh::lean_dec(v_declName_4832_);
                    state = 1;
                    continue;
                } else {
                    v_val_4861_ = leanh::lean_ctor_get(v___x_4860_, 0);
                    leanh::lean_inc(v_val_4861_);
                    leanh::lean_dec_ref_known(v___x_4860_, 1);
                    v___x_4862_ = l_Lean_Environment_header(v_env_4845_);
                    v_modules_4863_ = leanh::lean_ctor_get(v___x_4862_, 3);
                    leanh::lean_inc_ref(v_modules_4863_);
                    leanh::lean_dec_ref(v___x_4862_);
                    v___x_4864_ = lean_array_get_size(v_modules_4863_);
                    v___x_4865_ = lean_nat_dec_lt(v_val_4861_, v___x_4864_);
                    if v___x_4865_ == 0 {
                        leanh::lean_dec_ref(v_modules_4863_);
                        leanh::lean_dec(v_val_4861_);
                        leanh::lean_dec_ref(v_env_4845_);
                        leanh::lean_dec(v_declName_4832_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4866_ = lean_st_ref_get(v___y_4839_);
                        v_env_4867_ = leanh::lean_ctor_get(v___x_4866_, 0);
                        leanh::lean_inc_ref(v_env_4867_);
                        leanh::lean_dec(v___x_4866_);
                        v___x_4868_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__2);
                        v___x_4869_ = lean_array_fget(v_modules_4863_, v_val_4861_);
                        leanh::lean_dec(v_val_4861_);
                        leanh::lean_dec_ref(v_modules_4863_);
                        if v_isMeta_4833_ == 0 {
                            leanh::lean_dec_ref(v_env_4867_);
                            v___y_4871_ = v_isMeta_4833_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_declName_4832_);
                            v___x_4882_ = l_Lean_isMarkedMeta(v_env_4867_, v_declName_4832_);
                            if v___x_4882_ == 0 {
                                v___y_4871_ = v_isMeta_4833_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4883_ = 0;
                                v___y_4871_ = v___x_4883_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4843_ = leanh::lean_box(0);
                v___x_4844_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4844_, 0, v___x_4843_);
                return v___x_4844_;
            }
            2 => {
                v___x_4848_ = leanh::lean_box(0);
                v_sz_4849_ = lean_array_size(v___y_4847_);
                v___x_4850_ = 0usize;
                v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__1(v_env_4845_, v_declName_4832_, v___y_4847_, v_sz_4849_, v___x_4850_, v___x_4848_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
                leanh::lean_dec_ref(v___y_4847_);
                leanh::lean_dec_ref(v_env_4845_);
                if leanh::lean_obj_tag(v___x_4851_) == 0 {
                    v_isSharedCheck_4858_ = (!leanh::lean_is_exclusive(v___x_4851_)) as u8;
                    if v_isSharedCheck_4858_ == 0 {
                        v_unused_4859_ = leanh::lean_ctor_get(v___x_4851_, 0);
                        leanh::lean_dec(v_unused_4859_);
                        v___x_4853_ = v___x_4851_;
                        v_isShared_4854_ = v_isSharedCheck_4858_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4851_);
                        v___x_4853_ = leanh::lean_box(0);
                        v_isShared_4854_ = v_isSharedCheck_4858_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4851_;
                }
            }
            3 => {
                if v_isShared_4854_ == 0 {
                    leanh::lean_ctor_set(v___x_4853_, 0, v___x_4848_);
                    v___x_4856_ = v___x_4853_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4857_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4848_);
                    v___x_4856_ = v_reuseFailAlloc_4857_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4856_;
            }
            5 => {
                v_toImport_4872_ = leanh::lean_ctor_get(v___x_4869_, 0);
                leanh::lean_inc_ref(v_toImport_4872_);
                leanh::lean_dec(v___x_4869_);
                v_module_4873_ = leanh::lean_ctor_get(v_toImport_4872_, 0);
                leanh::lean_inc(v_module_4873_);
                leanh::lean_dec_ref(v_toImport_4872_);
                leanh::lean_inc(v_declName_4832_);
                v___x_4874_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0(v_module_4873_, v___y_4871_, v_declName_4832_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
                if leanh::lean_obj_tag(v___x_4874_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4874_, 1);
                    v___x_4875_ = l_Lean_indirectModUseExt;
                    v___x_4876_ = leanh::lean_box(1);
                    v___x_4877_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_env_4845_);
                    v___x_4878_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4868_,
                        v___x_4875_,
                        v_env_4845_,
                        v___x_4876_,
                        v___x_4877_,
                    );
                    v___x_4879_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v___x_4878_, v_declName_4832_);
                    leanh::lean_dec(v___x_4878_);
                    if leanh::lean_obj_tag(v___x_4879_) == 0 {
                        v___x_4880_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___closed__3;
                        v___y_4847_ = v___x_4880_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4881_ = leanh::lean_ctor_get(v___x_4879_, 0);
                        leanh::lean_inc(v_val_4881_);
                        leanh::lean_dec_ref_known(v___x_4879_, 1);
                        v___y_4847_ = v_val_4881_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_4845_);
                    leanh::lean_dec(v_declName_4832_);
                    return v___x_4874_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0___boxed(
    mut v_declName_4884_: *mut leanh::LeanObject,
    mut v_isMeta_4885_: *mut leanh::LeanObject,
    mut v___y_4886_: *mut leanh::LeanObject,
    mut v___y_4887_: *mut leanh::LeanObject,
    mut v___y_4888_: *mut leanh::LeanObject,
    mut v___y_4889_: *mut leanh::LeanObject,
    mut v___y_4890_: *mut leanh::LeanObject,
    mut v___y_4891_: *mut leanh::LeanObject,
    mut v___y_4892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_4893_: u8 = 0;
    let mut v_res_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4893_ = (leanh::lean_unbox(v_isMeta_4885_) as u8);
    v_res_4894_ =
        l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(
            v_declName_4884_,
            v_isMeta_boxed_4893_,
            v___y_4886_,
            v___y_4887_,
            v___y_4888_,
            v___y_4889_,
            v___y_4890_,
            v___y_4891_,
        );
    leanh::lean_dec(v___y_4891_);
    leanh::lean_dec_ref(v___y_4890_);
    leanh::lean_dec(v___y_4889_);
    leanh::lean_dec_ref(v___y_4888_);
    leanh::lean_dec(v___y_4887_);
    leanh::lean_dec_ref(v___y_4886_);
    return v_res_4894_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(
    mut v___x_4895_: *mut leanh::LeanObject,
    mut v___x_4896_: *mut leanh::LeanObject,
    mut v___y_4897_: *mut leanh::LeanObject,
    mut v___y_4898_: *mut leanh::LeanObject,
    mut v___y_4899_: *mut leanh::LeanObject,
    mut v___y_4900_: *mut leanh::LeanObject,
    mut v___y_4901_: *mut leanh::LeanObject,
    mut v___y_4902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4910_: u8 = 0;
    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_unused_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4919_: u8 = 0;
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4904_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                    v___x_4895_,
                    v___x_4896_,
                    v___y_4901_,
                    v___y_4902_,
                );
                if leanh::lean_obj_tag(v___x_4904_) == 0 {
                    v_a_4905_ = leanh::lean_ctor_get(v___x_4904_, 0);
                    leanh::lean_inc_n(v_a_4905_, 2);
                    leanh::lean_dec_ref_known(v___x_4904_, 1);
                    v___x_4906_ = 0;
                    v___x_4907_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0(v_a_4905_, v___x_4906_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
                    if leanh::lean_obj_tag(v___x_4907_) == 0 {
                        v_isSharedCheck_4914_ =
                            (!leanh::lean_is_exclusive(v___x_4907_)) as u8;
                        if v_isSharedCheck_4914_ == 0 {
                            v_unused_4915_ = leanh::lean_ctor_get(v___x_4907_, 0);
                            leanh::lean_dec(v_unused_4915_);
                            v___x_4909_ = v___x_4907_;
                            v_isShared_4910_ = v_isSharedCheck_4914_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4907_);
                            v___x_4909_ = leanh::lean_box(0);
                            v_isShared_4910_ = v_isSharedCheck_4914_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4905_);
                        v_a_4916_ = leanh::lean_ctor_get(v___x_4907_, 0);
                        v_isSharedCheck_4923_ =
                            (!leanh::lean_is_exclusive(v___x_4907_)) as u8;
                        if v_isSharedCheck_4923_ == 0 {
                            v___x_4918_ = v___x_4907_;
                            v_isShared_4919_ = v_isSharedCheck_4923_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4916_);
                            leanh::lean_dec(v___x_4907_);
                            v___x_4918_ = leanh::lean_box(0);
                            v_isShared_4919_ = v_isSharedCheck_4923_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_4904_;
                }
            }
            1 => {
                if v_isShared_4910_ == 0 {
                    leanh::lean_ctor_set(v___x_4909_, 0, v_a_4905_);
                    v___x_4912_ = v___x_4909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4913_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4905_);
                    v___x_4912_ = v_reuseFailAlloc_4913_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4912_;
            }
            3 => {
                if v_isShared_4919_ == 0 {
                    v___x_4921_ = v___x_4918_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
                    v___x_4921_ = v_reuseFailAlloc_4922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed(
    mut v___x_4924_: *mut leanh::LeanObject,
    mut v___x_4925_: *mut leanh::LeanObject,
    mut v___y_4926_: *mut leanh::LeanObject,
    mut v___y_4927_: *mut leanh::LeanObject,
    mut v___y_4928_: *mut leanh::LeanObject,
    mut v___y_4929_: *mut leanh::LeanObject,
    mut v___y_4930_: *mut leanh::LeanObject,
    mut v___y_4931_: *mut leanh::LeanObject,
    mut v___y_4932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4933_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0(
        v___x_4924_,
        v___x_4925_,
        v___y_4926_,
        v___y_4927_,
        v___y_4928_,
        v___y_4929_,
        v___y_4930_,
        v___y_4931_,
    );
    leanh::lean_dec(v___y_4931_);
    leanh::lean_dec_ref(v___y_4930_);
    leanh::lean_dec(v___y_4929_);
    leanh::lean_dec_ref(v___y_4928_);
    leanh::lean_dec(v___y_4927_);
    leanh::lean_dec_ref(v___y_4926_);
    return v_res_4933_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(
    mut v___y_4934_: *mut leanh::LeanObject,
    mut v_isExporting_4935_: u8,
    mut v___x_4936_: *mut leanh::LeanObject,
    mut v___y_4937_: *mut leanh::LeanObject,
    mut v___x_4938_: *mut leanh::LeanObject,
    mut v_a_x3f_4939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4964_: u8 = 0;
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4971_: u8 = 0;
    let mut v_unused_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4974_: u8 = 0;
    let mut v_unused_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4941_ = lean_st_ref_take(v___y_4934_);
                v_env_4942_ = leanh::lean_ctor_get(v___x_4941_, 0);
                v_nextMacroScope_4943_ = leanh::lean_ctor_get(v___x_4941_, 1);
                v_ngen_4944_ = leanh::lean_ctor_get(v___x_4941_, 2);
                v_auxDeclNGen_4945_ = leanh::lean_ctor_get(v___x_4941_, 3);
                v_traceState_4946_ = leanh::lean_ctor_get(v___x_4941_, 4);
                v_messages_4947_ = leanh::lean_ctor_get(v___x_4941_, 6);
                v_infoState_4948_ = leanh::lean_ctor_get(v___x_4941_, 7);
                v_snapshotTasks_4949_ = leanh::lean_ctor_get(v___x_4941_, 8);
                v_isSharedCheck_4974_ = (!leanh::lean_is_exclusive(v___x_4941_)) as u8;
                if v_isSharedCheck_4974_ == 0 {
                    v_unused_4975_ = leanh::lean_ctor_get(v___x_4941_, 5);
                    leanh::lean_dec(v_unused_4975_);
                    v___x_4951_ = v___x_4941_;
                    v_isShared_4952_ = v_isSharedCheck_4974_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4949_);
                    leanh::lean_inc(v_infoState_4948_);
                    leanh::lean_inc(v_messages_4947_);
                    leanh::lean_inc(v_traceState_4946_);
                    leanh::lean_inc(v_auxDeclNGen_4945_);
                    leanh::lean_inc(v_ngen_4944_);
                    leanh::lean_inc(v_nextMacroScope_4943_);
                    leanh::lean_inc(v_env_4942_);
                    leanh::lean_dec(v___x_4941_);
                    v___x_4951_ = leanh::lean_box(0);
                    v_isShared_4952_ = v_isSharedCheck_4974_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4953_ = l_Lean_Environment_setExporting(v_env_4942_, v_isExporting_4935_);
                if v_isShared_4952_ == 0 {
                    leanh::lean_ctor_set(v___x_4951_, 5, v___x_4936_);
                    leanh::lean_ctor_set(v___x_4951_, 0, v___x_4953_);
                    v___x_4955_ = v___x_4951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4953_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 1, v_nextMacroScope_4943_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 2, v_ngen_4944_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 3, v_auxDeclNGen_4945_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 4, v_traceState_4946_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 5, v___x_4936_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 6, v_messages_4947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 7, v_infoState_4948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 8, v_snapshotTasks_4949_);
                    v___x_4955_ = v_reuseFailAlloc_4973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4956_ = lean_st_ref_set(v___y_4934_, v___x_4955_);
                v___x_4957_ = lean_st_ref_take(v___y_4937_);
                v_mctx_4958_ = leanh::lean_ctor_get(v___x_4957_, 0);
                v_zetaDeltaFVarIds_4959_ = leanh::lean_ctor_get(v___x_4957_, 2);
                v_postponed_4960_ = leanh::lean_ctor_get(v___x_4957_, 3);
                v_diag_4961_ = leanh::lean_ctor_get(v___x_4957_, 4);
                v_isSharedCheck_4971_ = (!leanh::lean_is_exclusive(v___x_4957_)) as u8;
                if v_isSharedCheck_4971_ == 0 {
                    v_unused_4972_ = leanh::lean_ctor_get(v___x_4957_, 1);
                    leanh::lean_dec(v_unused_4972_);
                    v___x_4963_ = v___x_4957_;
                    v_isShared_4964_ = v_isSharedCheck_4971_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_4961_);
                    leanh::lean_inc(v_postponed_4960_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_4959_);
                    leanh::lean_inc(v_mctx_4958_);
                    leanh::lean_dec(v___x_4957_);
                    v___x_4963_ = leanh::lean_box(0);
                    v_isShared_4964_ = v_isSharedCheck_4971_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4964_ == 0 {
                    leanh::lean_ctor_set(v___x_4963_, 1, v___x_4938_);
                    v___x_4966_ = v___x_4963_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4970_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_mctx_4958_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4970_, 1, v___x_4938_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4970_,
                        2,
                        v_zetaDeltaFVarIds_4959_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4970_, 3, v_postponed_4960_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4970_, 4, v_diag_4961_);
                    v___x_4966_ = v_reuseFailAlloc_4970_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4967_ = lean_st_ref_set(v___y_4937_, v___x_4966_);
                v___x_4968_ = leanh::lean_box(0);
                v___x_4969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4969_, 0, v___x_4968_);
                return v___x_4969_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0___boxed(
    mut v___y_4976_: *mut leanh::LeanObject,
    mut v_isExporting_4977_: *mut leanh::LeanObject,
    mut v___x_4978_: *mut leanh::LeanObject,
    mut v___y_4979_: *mut leanh::LeanObject,
    mut v___x_4980_: *mut leanh::LeanObject,
    mut v_a_x3f_4981_: *mut leanh::LeanObject,
    mut v___y_4982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4983_: u8 = 0;
    let mut v_res_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4983_ = (leanh::lean_unbox(v_isExporting_4977_) as u8);
    v_res_4984_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_4976_, v_isExporting_boxed_4983_, v___x_4978_, v___y_4979_, v___x_4980_, v_a_x3f_4981_);
    leanh::lean_dec(v_a_x3f_4981_);
    leanh::lean_dec(v___y_4979_);
    leanh::lean_dec(v___y_4976_);
    return v_res_4984_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(
    mut v_x_4985_: *mut leanh::LeanObject,
    mut v_isExporting_4986_: u8,
    mut v___y_4987_: *mut leanh::LeanObject,
    mut v___y_4988_: *mut leanh::LeanObject,
    mut v___y_4989_: *mut leanh::LeanObject,
    mut v___y_4990_: *mut leanh::LeanObject,
    mut v___y_4991_: *mut leanh::LeanObject,
    mut v___y_4992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4996_: u8 = 0;
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5021_: u8 = 0;
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5030_: u8 = 0;
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5036_: u8 = 0;
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5040_: u8 = 0;
    let mut v_unused_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5043_: u8 = 0;
    let mut v_a_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5053_: u8 = 0;
    let mut v_unused_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5056_: u8 = 0;
    let mut v_unused_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v_unused_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4994_ = lean_st_ref_get(v___y_4992_);
                v_env_4995_ = leanh::lean_ctor_get(v___x_4994_, 0);
                leanh::lean_inc_ref(v_env_4995_);
                leanh::lean_dec(v___x_4994_);
                v_isExporting_4996_ = leanh::lean_ctor_get_uint8(
                    v_env_4995_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_4995_);
                v___x_4997_ = lean_st_ref_take(v___y_4992_);
                v_env_4998_ = leanh::lean_ctor_get(v___x_4997_, 0);
                v_nextMacroScope_4999_ = leanh::lean_ctor_get(v___x_4997_, 1);
                v_ngen_5000_ = leanh::lean_ctor_get(v___x_4997_, 2);
                v_auxDeclNGen_5001_ = leanh::lean_ctor_get(v___x_4997_, 3);
                v_traceState_5002_ = leanh::lean_ctor_get(v___x_4997_, 4);
                v_messages_5003_ = leanh::lean_ctor_get(v___x_4997_, 6);
                v_infoState_5004_ = leanh::lean_ctor_get(v___x_4997_, 7);
                v_snapshotTasks_5005_ = leanh::lean_ctor_get(v___x_4997_, 8);
                v_isSharedCheck_5059_ = (!leanh::lean_is_exclusive(v___x_4997_)) as u8;
                if v_isSharedCheck_5059_ == 0 {
                    v_unused_5060_ = leanh::lean_ctor_get(v___x_4997_, 5);
                    leanh::lean_dec(v_unused_5060_);
                    v___x_5007_ = v___x_4997_;
                    v_isShared_5008_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5005_);
                    leanh::lean_inc(v_infoState_5004_);
                    leanh::lean_inc(v_messages_5003_);
                    leanh::lean_inc(v_traceState_5002_);
                    leanh::lean_inc(v_auxDeclNGen_5001_);
                    leanh::lean_inc(v_ngen_5000_);
                    leanh::lean_inc(v_nextMacroScope_4999_);
                    leanh::lean_inc(v_env_4998_);
                    leanh::lean_dec(v___x_4997_);
                    v___x_5007_ = leanh::lean_box(0);
                    v_isShared_5008_ = v_isSharedCheck_5059_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5009_ = l_Lean_Environment_setExporting(v_env_4998_, v_isExporting_4986_);
                v___x_5010_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__5);
                if v_isShared_5008_ == 0 {
                    leanh::lean_ctor_set(v___x_5007_, 5, v___x_5010_);
                    leanh::lean_ctor_set(v___x_5007_, 0, v___x_5009_);
                    v___x_5012_ = v___x_5007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5058_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 1, v_nextMacroScope_4999_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 2, v_ngen_5000_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 3, v_auxDeclNGen_5001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 4, v_traceState_5002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 5, v___x_5010_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 6, v_messages_5003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 7, v_infoState_5004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 8, v_snapshotTasks_5005_);
                    v___x_5012_ = v_reuseFailAlloc_5058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5013_ = lean_st_ref_set(v___y_4992_, v___x_5012_);
                v___x_5014_ = lean_st_ref_take(v___y_4990_);
                v_mctx_5015_ = leanh::lean_ctor_get(v___x_5014_, 0);
                v_zetaDeltaFVarIds_5016_ = leanh::lean_ctor_get(v___x_5014_, 2);
                v_postponed_5017_ = leanh::lean_ctor_get(v___x_5014_, 3);
                v_diag_5018_ = leanh::lean_ctor_get(v___x_5014_, 4);
                v_isSharedCheck_5056_ = (!leanh::lean_is_exclusive(v___x_5014_)) as u8;
                if v_isSharedCheck_5056_ == 0 {
                    v_unused_5057_ = leanh::lean_ctor_get(v___x_5014_, 1);
                    leanh::lean_dec(v_unused_5057_);
                    v___x_5020_ = v___x_5014_;
                    v_isShared_5021_ = v_isSharedCheck_5056_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5018_);
                    leanh::lean_inc(v_postponed_5017_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5016_);
                    leanh::lean_inc(v_mctx_5015_);
                    leanh::lean_dec(v___x_5014_);
                    v___x_5020_ = leanh::lean_box(0);
                    v_isShared_5021_ = v_isSharedCheck_5056_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5022_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0___closed__6);
                if v_isShared_5021_ == 0 {
                    leanh::lean_ctor_set(v___x_5020_, 1, v___x_5022_);
                    v___x_5024_ = v___x_5020_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5055_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 0, v_mctx_5015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 1, v___x_5022_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5055_,
                        2,
                        v_zetaDeltaFVarIds_5016_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 3, v_postponed_5017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5055_, 4, v_diag_5018_);
                    v___x_5024_ = v_reuseFailAlloc_5055_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5025_ = lean_st_ref_set(v___y_4990_, v___x_5024_);
                leanh::lean_inc(v___y_4992_);
                leanh::lean_inc_ref(v___y_4991_);
                leanh::lean_inc(v___y_4990_);
                leanh::lean_inc_ref(v___y_4989_);
                leanh::lean_inc(v___y_4988_);
                leanh::lean_inc_ref(v___y_4987_);
                v_r_5026_ = leanh::lean_apply_7(
                    v_x_4985_,
                    v___y_4987_,
                    v___y_4988_,
                    v___y_4989_,
                    v___y_4990_,
                    v___y_4991_,
                    v___y_4992_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_5026_) == 0 {
                    v_a_5027_ = leanh::lean_ctor_get(v_r_5026_, 0);
                    v_isSharedCheck_5043_ = (!leanh::lean_is_exclusive(v_r_5026_)) as u8;
                    if v_isSharedCheck_5043_ == 0 {
                        v___x_5029_ = v_r_5026_;
                        v_isShared_5030_ = v_isSharedCheck_5043_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5027_);
                        leanh::lean_dec(v_r_5026_);
                        v___x_5029_ = leanh::lean_box(0);
                        v_isShared_5030_ = v_isSharedCheck_5043_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_5044_ = leanh::lean_ctor_get(v_r_5026_, 0);
                    leanh::lean_inc(v_a_5044_);
                    leanh::lean_dec_ref_known(v_r_5026_, 1);
                    v___x_5045_ = leanh::lean_box(0);
                    v___x_5046_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_4992_, v_isExporting_4996_, v___x_5010_, v___y_4990_, v___x_5022_, v___x_5045_);
                    v_isSharedCheck_5053_ = (!leanh::lean_is_exclusive(v___x_5046_)) as u8;
                    if v_isSharedCheck_5053_ == 0 {
                        v_unused_5054_ = leanh::lean_ctor_get(v___x_5046_, 0);
                        leanh::lean_dec(v_unused_5054_);
                        v___x_5048_ = v___x_5046_;
                        v_isShared_5049_ = v_isSharedCheck_5053_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5046_);
                        v___x_5048_ = leanh::lean_box(0);
                        v_isShared_5049_ = v_isSharedCheck_5053_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                leanh::lean_inc(v_a_5027_);
                if v_isShared_5030_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5029_, 1);
                    v___x_5032_ = v___x_5029_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5042_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5042_, 0, v_a_5027_);
                    v___x_5032_ = v_reuseFailAlloc_5042_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5033_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___lam__0(v___y_4992_, v_isExporting_4996_, v___x_5010_, v___y_4990_, v___x_5022_, v___x_5032_);
                leanh::lean_dec_ref(v___x_5032_);
                v_isSharedCheck_5040_ = (!leanh::lean_is_exclusive(v___x_5033_)) as u8;
                if v_isSharedCheck_5040_ == 0 {
                    v_unused_5041_ = leanh::lean_ctor_get(v___x_5033_, 0);
                    leanh::lean_dec(v_unused_5041_);
                    v___x_5035_ = v___x_5033_;
                    v_isShared_5036_ = v_isSharedCheck_5040_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v___x_5033_);
                    v___x_5035_ = leanh::lean_box(0);
                    v_isShared_5036_ = v_isSharedCheck_5040_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_5036_ == 0 {
                    leanh::lean_ctor_set(v___x_5035_, 0, v_a_5027_);
                    v___x_5038_ = v___x_5035_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5039_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5039_, 0, v_a_5027_);
                    v___x_5038_ = v_reuseFailAlloc_5039_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5038_;
            }
            9 => {
                if v_isShared_5049_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5048_, 1);
                    leanh::lean_ctor_set(v___x_5048_, 0, v_a_5044_);
                    v___x_5051_ = v___x_5048_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5052_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5044_);
                    v___x_5051_ = v_reuseFailAlloc_5052_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5051_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg___boxed(
    mut v_x_5061_: *mut leanh::LeanObject,
    mut v_isExporting_5062_: *mut leanh::LeanObject,
    mut v___y_5063_: *mut leanh::LeanObject,
    mut v___y_5064_: *mut leanh::LeanObject,
    mut v___y_5065_: *mut leanh::LeanObject,
    mut v___y_5066_: *mut leanh::LeanObject,
    mut v___y_5067_: *mut leanh::LeanObject,
    mut v___y_5068_: *mut leanh::LeanObject,
    mut v___y_5069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_5070_: u8 = 0;
    let mut v_res_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5070_ = (leanh::lean_unbox(v_isExporting_5062_) as u8);
    v_res_5071_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_5061_, v_isExporting_boxed_5070_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
    leanh::lean_dec(v___y_5068_);
    leanh::lean_dec_ref(v___y_5067_);
    leanh::lean_dec(v___y_5066_);
    leanh::lean_dec_ref(v___y_5065_);
    leanh::lean_dec(v___y_5064_);
    leanh::lean_dec_ref(v___y_5063_);
    return v_res_5071_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(
    mut v_x_5072_: *mut leanh::LeanObject,
    mut v_when_5073_: u8,
    mut v___y_5074_: *mut leanh::LeanObject,
    mut v___y_5075_: *mut leanh::LeanObject,
    mut v___y_5076_: *mut leanh::LeanObject,
    mut v___y_5077_: *mut leanh::LeanObject,
    mut v___y_5078_: *mut leanh::LeanObject,
    mut v___y_5079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_5073_ == 0 {
        let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_5079_);
        leanh::lean_inc_ref(v___y_5078_);
        leanh::lean_inc(v___y_5077_);
        leanh::lean_inc_ref(v___y_5076_);
        leanh::lean_inc(v___y_5075_);
        leanh::lean_inc_ref(v___y_5074_);
        v___x_5081_ = leanh::lean_apply_7(
            v_x_5072_,
            v___y_5074_,
            v___y_5075_,
            v___y_5076_,
            v___y_5077_,
            v___y_5078_,
            v___y_5079_,
            leanh::lean_box(0),
        );
        return v___x_5081_;
    } else {
        let mut v___x_5082_: u8 = 0;
        let mut v___x_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5082_ = 0;
        v___x_5083_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_5072_, v___x_5082_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_);
        return v___x_5083_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg___boxed(
    mut v_x_5084_: *mut leanh::LeanObject,
    mut v_when_5085_: *mut leanh::LeanObject,
    mut v___y_5086_: *mut leanh::LeanObject,
    mut v___y_5087_: *mut leanh::LeanObject,
    mut v___y_5088_: *mut leanh::LeanObject,
    mut v___y_5089_: *mut leanh::LeanObject,
    mut v___y_5090_: *mut leanh::LeanObject,
    mut v___y_5091_: *mut leanh::LeanObject,
    mut v___y_5092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_5093_: u8 = 0;
    let mut v_res_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_5093_ = (leanh::lean_unbox(v_when_5085_) as u8);
    v_res_5094_ =
        l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(
            v_x_5084_,
            v_when_boxed_5093_,
            v___y_5086_,
            v___y_5087_,
            v___y_5088_,
            v___y_5089_,
            v___y_5090_,
            v___y_5091_,
        );
    leanh::lean_dec(v___y_5091_);
    leanh::lean_dec_ref(v___y_5090_);
    leanh::lean_dec(v___y_5089_);
    leanh::lean_dec_ref(v___y_5088_);
    leanh::lean_dec(v___y_5087_);
    leanh::lean_dec_ref(v___y_5086_);
    return v_res_5094_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(
    mut v___x_5096_: *mut leanh::LeanObject,
    mut v___x_5097_: *mut leanh::LeanObject,
    mut v_____r_5098_: *mut leanh::LeanObject,
    mut v___y_5099_: *mut leanh::LeanObject,
    mut v___y_5100_: *mut leanh::LeanObject,
    mut v___y_5101_: *mut leanh::LeanObject,
    mut v___y_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    v___x_5106_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__12;
    v___x_5107_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__13;
    v___x_5108_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___closed__0;
    v___x_5109_ = l_Lean_Name_mkStr4(v___x_5096_, v___x_5106_, v___x_5107_, v___x_5108_);
    leanh::lean_inc(v___x_5097_);
    v___x_5110_ = l_Lean_Syntax_isOfKind(v___x_5097_, v___x_5109_);
    leanh::lean_dec(v___x_5109_);
    if v___x_5110_ == 0 {
        let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_5097_);
        v___x_5111_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
        return v___x_5111_;
    } else {
        let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5112_ = leanh::lean_unsigned_to_nat(2);
        v___x_5113_ = l_Lean_Syntax_getArg(v___x_5097_, v___x_5112_);
        leanh::lean_dec(v___x_5097_);
        v___x_5114_ = leanh::lean_box(0);
        v___f_5115_ = leanh::lean_alloc_closure(
            l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        leanh::lean_closure_set(v___f_5115_, 0, v___x_5113_);
        leanh::lean_closure_set(v___f_5115_, 1, v___x_5114_);
        v___x_5116_ = l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(v___f_5115_, v___x_5110_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
        return v___x_5116_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1___boxed(
    mut v___x_5117_: *mut leanh::LeanObject,
    mut v___x_5118_: *mut leanh::LeanObject,
    mut v_____r_5119_: *mut leanh::LeanObject,
    mut v___y_5120_: *mut leanh::LeanObject,
    mut v___y_5121_: *mut leanh::LeanObject,
    mut v___y_5122_: *mut leanh::LeanObject,
    mut v___y_5123_: *mut leanh::LeanObject,
    mut v___y_5124_: *mut leanh::LeanObject,
    mut v___y_5125_: *mut leanh::LeanObject,
    mut v___y_5126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5127_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(
        v___x_5117_,
        v___x_5118_,
        v_____r_5119_,
        v___y_5120_,
        v___y_5121_,
        v___y_5122_,
        v___y_5123_,
        v___y_5124_,
        v___y_5125_,
    );
    leanh::lean_dec(v___y_5125_);
    leanh::lean_dec_ref(v___y_5124_);
    leanh::lean_dec(v___y_5123_);
    leanh::lean_dec_ref(v___y_5122_);
    leanh::lean_dec(v___y_5121_);
    leanh::lean_dec_ref(v___y_5120_);
    return v_res_5127_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5132_ = leanh::lean_box(0);
    v___x_5133_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1;
    v___x_5134_ = l_Lean_mkConst(v___x_5133_, v___x_5132_);
    return v___x_5134_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2,
    );
    v___x_5136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5136_, 0, v___x_5135_);
    return v___x_5136_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(
    mut v_a_5143_: *mut leanh::LeanObject,
    mut v_a_5144_: *mut leanh::LeanObject,
    mut v_a_5145_: *mut leanh::LeanObject,
    mut v_a_5146_: *mut leanh::LeanObject,
    mut v_a_5147_: *mut leanh::LeanObject,
    mut v_a_5148_: *mut leanh::LeanObject,
    mut v_a_5149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5163_: u8 = 0;
    let mut v_cancelTk_x3f_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5165_: u8 = 0;
    let mut v_inheritedTraceOptions_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5172_: u8 = 0;
    let mut v___x_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: u8 = 0;
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5183_: u8 = 0;
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5187_: u8 = 0;
    let mut v_unused_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5192_: u8 = 0;
    let mut v___x_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5196_: u8 = 0;
    let mut v___y_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5203_: u8 = 0;
    let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5207_: u8 = 0;
    let mut v___x_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: u8 = 0;
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5151_ = leanh::lean_ctor_get(v_a_5148_, 0);
                v_fileMap_5152_ = leanh::lean_ctor_get(v_a_5148_, 1);
                v_options_5153_ = leanh::lean_ctor_get(v_a_5148_, 2);
                v_currRecDepth_5154_ = leanh::lean_ctor_get(v_a_5148_, 3);
                v_maxRecDepth_5155_ = leanh::lean_ctor_get(v_a_5148_, 4);
                v_ref_5156_ = leanh::lean_ctor_get(v_a_5148_, 5);
                v_currNamespace_5157_ = leanh::lean_ctor_get(v_a_5148_, 6);
                v_openDecls_5158_ = leanh::lean_ctor_get(v_a_5148_, 7);
                v_initHeartbeats_5159_ = leanh::lean_ctor_get(v_a_5148_, 8);
                v_maxHeartbeats_5160_ = leanh::lean_ctor_get(v_a_5148_, 9);
                v_quotContext_5161_ = leanh::lean_ctor_get(v_a_5148_, 10);
                v_currMacroScope_5162_ = leanh::lean_ctor_get(v_a_5148_, 11);
                v_diag_5163_ = leanh::lean_ctor_get_uint8(
                    v_a_5148_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5164_ = leanh::lean_ctor_get(v_a_5148_, 12);
                v_suppressElabErrors_5165_ = leanh::lean_ctor_get_uint8(
                    v_a_5148_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5166_ = leanh::lean_ctor_get(v_a_5148_, 13);
                v___x_5167_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__11;
                leanh::lean_inc(v_a_5143_);
                v___x_5208_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_a_5143_,
                    );
                v_ref_5209_ = l_Lean_replaceRef(v_a_5143_, v_ref_5156_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_5166_);
                leanh::lean_inc(v_cancelTk_x3f_5164_);
                leanh::lean_inc(v_currMacroScope_5162_);
                leanh::lean_inc(v_quotContext_5161_);
                leanh::lean_inc(v_maxHeartbeats_5160_);
                leanh::lean_inc(v_initHeartbeats_5159_);
                leanh::lean_inc(v_openDecls_5158_);
                leanh::lean_inc(v_currNamespace_5157_);
                leanh::lean_inc(v_maxRecDepth_5155_);
                leanh::lean_inc(v_currRecDepth_5154_);
                leanh::lean_inc_ref(v_options_5153_);
                leanh::lean_inc_ref(v_fileMap_5152_);
                leanh::lean_inc_ref(v_fileName_5151_);
                v___x_5210_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_5210_, 0, v_fileName_5151_);
                leanh::lean_ctor_set(v___x_5210_, 1, v_fileMap_5152_);
                leanh::lean_ctor_set(v___x_5210_, 2, v_options_5153_);
                leanh::lean_ctor_set(v___x_5210_, 3, v_currRecDepth_5154_);
                leanh::lean_ctor_set(v___x_5210_, 4, v_maxRecDepth_5155_);
                leanh::lean_ctor_set(v___x_5210_, 5, v_ref_5209_);
                leanh::lean_ctor_set(v___x_5210_, 6, v_currNamespace_5157_);
                leanh::lean_ctor_set(v___x_5210_, 7, v_openDecls_5158_);
                leanh::lean_ctor_set(v___x_5210_, 8, v_initHeartbeats_5159_);
                leanh::lean_ctor_set(v___x_5210_, 9, v_maxHeartbeats_5160_);
                leanh::lean_ctor_set(v___x_5210_, 10, v_quotContext_5161_);
                leanh::lean_ctor_set(v___x_5210_, 11, v_currMacroScope_5162_);
                leanh::lean_ctor_set(v___x_5210_, 12, v_cancelTk_x3f_5164_);
                leanh::lean_ctor_set(v___x_5210_, 13, v_inheritedTraceOptions_5166_);
                leanh::lean_ctor_set_uint8(
                    v___x_5210_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_5163_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5210_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5165_,
                );
                v___x_5211_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__5;
                leanh::lean_inc(v___x_5208_);
                v___x_5212_ = l_Lean_Syntax_isOfKind(v___x_5208_, v___x_5211_);
                if v___x_5212_ == 0 {
                    v___x_5213_ = leanh::lean_box(0);
                    v___x_5214_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(
                        v___x_5167_,
                        v___x_5208_,
                        v___x_5213_,
                        v_a_5144_,
                        v_a_5145_,
                        v_a_5146_,
                        v_a_5147_,
                        v___x_5210_,
                        v_a_5149_,
                    );
                    leanh::lean_dec_ref_known(v___x_5210_, 14);
                    v___y_5198_ = v___x_5214_;
                    state = 6;
                    continue;
                } else {
                    v___x_5215_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5216_ = l_Lean_Syntax_getArg(v___x_5208_, v___x_5215_);
                    v___x_5217_ = l_Lean_Syntax_isNameLit_x3f(v___x_5216_);
                    leanh::lean_dec(v___x_5216_);
                    if leanh::lean_obj_tag(v___x_5217_) == 1 {
                        leanh::lean_dec_ref_known(v___x_5210_, 14);
                        leanh::lean_dec(v___x_5208_);
                        v_val_5218_ = leanh::lean_ctor_get(v___x_5217_, 0);
                        leanh::lean_inc(v_val_5218_);
                        leanh::lean_dec_ref_known(v___x_5217_, 1);
                        v_a_5169_ = v_val_5218_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5217_);
                        v___x_5219_ = leanh::lean_box(0);
                        v___x_5220_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___lam__1(
                            v___x_5167_,
                            v___x_5208_,
                            v___x_5219_,
                            v_a_5144_,
                            v_a_5145_,
                            v_a_5146_,
                            v_a_5147_,
                            v___x_5210_,
                            v_a_5149_,
                        );
                        leanh::lean_dec_ref_known(v___x_5210_, 14);
                        v___y_5198_ = v___x_5220_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5170_ = lean_st_ref_get(v_a_5149_);
                v_infoState_5171_ = leanh::lean_ctor_get(v___x_5170_, 7);
                leanh::lean_inc_ref(v_infoState_5171_);
                leanh::lean_dec(v___x_5170_);
                v_enabled_5172_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5171_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5171_);
                leanh::lean_inc(v_a_5169_);
                v___x_5173_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_5169_);
                leanh::lean_inc_ref(v___x_5173_);
                v___x_5174_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5174_, 0, v_a_5169_);
                leanh::lean_ctor_set(v___x_5174_, 1, v___x_5173_);
                if v_enabled_5172_ == 0 {
                    leanh::lean_dec_ref(v___x_5173_);
                    leanh::lean_dec(v_a_5143_);
                    v___x_5175_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5175_, 0, v___x_5174_);
                    return v___x_5175_;
                } else {
                    v___x_5176_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3,
                    );
                    v___x_5177_ = leanh::lean_box(0);
                    v___x_5178_ = leanh::lean_box(0);
                    v___x_5179_ = 0;
                    v___x_5180_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_a_5143_,
                        v___x_5173_,
                        v___x_5176_,
                        v___x_5177_,
                        v___x_5178_,
                        v___x_5179_,
                        v___x_5179_,
                        v_a_5144_,
                        v_a_5145_,
                        v_a_5146_,
                        v_a_5147_,
                        v_a_5148_,
                        v_a_5149_,
                    );
                    if leanh::lean_obj_tag(v___x_5180_) == 0 {
                        v_isSharedCheck_5187_ =
                            (!leanh::lean_is_exclusive(v___x_5180_)) as u8;
                        if v_isSharedCheck_5187_ == 0 {
                            v_unused_5188_ = leanh::lean_ctor_get(v___x_5180_, 0);
                            leanh::lean_dec(v_unused_5188_);
                            v___x_5182_ = v___x_5180_;
                            v_isShared_5183_ = v_isSharedCheck_5187_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5180_);
                            v___x_5182_ = leanh::lean_box(0);
                            v_isShared_5183_ = v_isSharedCheck_5187_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_5174_, 2);
                        v_a_5189_ = leanh::lean_ctor_get(v___x_5180_, 0);
                        v_isSharedCheck_5196_ =
                            (!leanh::lean_is_exclusive(v___x_5180_)) as u8;
                        if v_isSharedCheck_5196_ == 0 {
                            v___x_5191_ = v___x_5180_;
                            v_isShared_5192_ = v_isSharedCheck_5196_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5189_);
                            leanh::lean_dec(v___x_5180_);
                            v___x_5191_ = leanh::lean_box(0);
                            v_isShared_5192_ = v_isSharedCheck_5196_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5183_ == 0 {
                    leanh::lean_ctor_set(v___x_5182_, 0, v___x_5174_);
                    v___x_5185_ = v___x_5182_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 0, v___x_5174_);
                    v___x_5185_ = v_reuseFailAlloc_5186_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5185_;
            }
            4 => {
                if v_isShared_5192_ == 0 {
                    v___x_5194_ = v___x_5191_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5195_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_a_5189_);
                    v___x_5194_ = v_reuseFailAlloc_5195_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5194_;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_5198_) == 0 {
                    v_a_5199_ = leanh::lean_ctor_get(v___y_5198_, 0);
                    leanh::lean_inc(v_a_5199_);
                    leanh::lean_dec_ref_known(v___y_5198_, 1);
                    v_a_5169_ = v_a_5199_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_5143_);
                    v_a_5200_ = leanh::lean_ctor_get(v___y_5198_, 0);
                    v_isSharedCheck_5207_ = (!leanh::lean_is_exclusive(v___y_5198_)) as u8;
                    if v_isSharedCheck_5207_ == 0 {
                        v___x_5202_ = v___y_5198_;
                        v_isShared_5203_ = v_isSharedCheck_5207_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5200_);
                        leanh::lean_dec(v___y_5198_);
                        v___x_5202_ = leanh::lean_box(0);
                        v_isShared_5203_ = v_isSharedCheck_5207_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5203_ == 0 {
                    v___x_5205_ = v___x_5202_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_a_5200_);
                    v___x_5205_ = v_reuseFailAlloc_5206_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___boxed(
    mut v_a_5221_: *mut leanh::LeanObject,
    mut v_a_5222_: *mut leanh::LeanObject,
    mut v_a_5223_: *mut leanh::LeanObject,
    mut v_a_5224_: *mut leanh::LeanObject,
    mut v_a_5225_: *mut leanh::LeanObject,
    mut v_a_5226_: *mut leanh::LeanObject,
    mut v_a_5227_: *mut leanh::LeanObject,
    mut v_a_5228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5229_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(
        v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_,
    );
    leanh::lean_dec(v_a_5227_);
    leanh::lean_dec_ref(v_a_5226_);
    leanh::lean_dec(v_a_5225_);
    leanh::lean_dec_ref(v_a_5224_);
    leanh::lean_dec(v_a_5223_);
    leanh::lean_dec_ref(v_a_5222_);
    return v_res_5229_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(
    mut v_00_u03b1_5230_: *mut leanh::LeanObject,
    mut v_x_5231_: *mut leanh::LeanObject,
    mut v_isExporting_5232_: u8,
    mut v___y_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
    mut v___y_5238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5240_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___redArg(v_x_5231_, v_isExporting_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_, v___y_5237_, v___y_5238_);
    return v___x_5240_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4___boxed(
    mut v_00_u03b1_5241_: *mut leanh::LeanObject,
    mut v_x_5242_: *mut leanh::LeanObject,
    mut v_isExporting_5243_: *mut leanh::LeanObject,
    mut v___y_5244_: *mut leanh::LeanObject,
    mut v___y_5245_: *mut leanh::LeanObject,
    mut v___y_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
    mut v___y_5249_: *mut leanh::LeanObject,
    mut v___y_5250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_5251_: u8 = 0;
    let mut v_res_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_5251_ = (leanh::lean_unbox(v_isExporting_5243_) as u8);
    v_res_5252_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1_spec__4(v_00_u03b1_5241_, v_x_5242_, v_isExporting_boxed_5251_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_, v___y_5249_);
    leanh::lean_dec(v___y_5249_);
    leanh::lean_dec_ref(v___y_5248_);
    leanh::lean_dec(v___y_5247_);
    leanh::lean_dec_ref(v___y_5246_);
    leanh::lean_dec(v___y_5245_);
    leanh::lean_dec_ref(v___y_5244_);
    return v_res_5252_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(
    mut v_00_u03b1_5253_: *mut leanh::LeanObject,
    mut v_x_5254_: *mut leanh::LeanObject,
    mut v_when_5255_: u8,
    mut v___y_5256_: *mut leanh::LeanObject,
    mut v___y_5257_: *mut leanh::LeanObject,
    mut v___y_5258_: *mut leanh::LeanObject,
    mut v___y_5259_: *mut leanh::LeanObject,
    mut v___y_5260_: *mut leanh::LeanObject,
    mut v___y_5261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5263_ =
        l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___redArg(
            v_x_5254_,
            v_when_5255_,
            v___y_5256_,
            v___y_5257_,
            v___y_5258_,
            v___y_5259_,
            v___y_5260_,
            v___y_5261_,
        );
    return v___x_5263_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1___boxed(
    mut v_00_u03b1_5264_: *mut leanh::LeanObject,
    mut v_x_5265_: *mut leanh::LeanObject,
    mut v_when_5266_: *mut leanh::LeanObject,
    mut v___y_5267_: *mut leanh::LeanObject,
    mut v___y_5268_: *mut leanh::LeanObject,
    mut v___y_5269_: *mut leanh::LeanObject,
    mut v___y_5270_: *mut leanh::LeanObject,
    mut v___y_5271_: *mut leanh::LeanObject,
    mut v___y_5272_: *mut leanh::LeanObject,
    mut v___y_5273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_5274_: u8 = 0;
    let mut v_res_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_5274_ = (leanh::lean_unbox(v_when_5266_) as u8);
    v_res_5275_ =
        l_Lean_withoutExporting___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__1(
            v_00_u03b1_5264_,
            v_x_5265_,
            v_when_boxed_5274_,
            v___y_5267_,
            v___y_5268_,
            v___y_5269_,
            v___y_5270_,
            v___y_5271_,
            v___y_5272_,
        );
    leanh::lean_dec(v___y_5272_);
    leanh::lean_dec_ref(v___y_5271_);
    leanh::lean_dec(v___y_5270_);
    leanh::lean_dec_ref(v___y_5269_);
    leanh::lean_dec(v___y_5268_);
    leanh::lean_dec_ref(v___y_5267_);
    return v_res_5275_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(
    mut v_00_u03b2_5276_: *mut leanh::LeanObject,
    mut v_m_5277_: *mut leanh::LeanObject,
    mut v_a_5278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___redArg(v_m_5277_, v_a_5278_);
    return v___x_5279_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2___boxed(
    mut v_00_u03b2_5280_: *mut leanh::LeanObject,
    mut v_m_5281_: *mut leanh::LeanObject,
    mut v_a_5282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2(v_00_u03b2_5280_, v_m_5281_, v_a_5282_);
    leanh::lean_dec(v_a_5282_);
    leanh::lean_dec_ref(v_m_5281_);
    return v_res_5283_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5284_: *mut leanh::LeanObject,
    mut v_x_5285_: *mut leanh::LeanObject,
    mut v_x_5286_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5287_: u8 = 0;
    v___x_5287_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___redArg(v_x_5285_, v_x_5286_);
    return v___x_5287_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_5288_: *mut leanh::LeanObject,
    mut v_x_5289_: *mut leanh::LeanObject,
    mut v_x_5290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5291_: u8 = 0;
    let mut v_r_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5291_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1(v_00_u03b2_5288_, v_x_5289_, v_x_5290_);
    leanh::lean_dec_ref(v_x_5290_);
    leanh::lean_dec_ref(v_x_5289_);
    v_r_5292_ = leanh::lean_box((v_res_5291_) as usize);
    return v_r_5292_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(
    mut v_cls_5293_: *mut leanh::LeanObject,
    mut v_msg_5294_: *mut leanh::LeanObject,
    mut v___y_5295_: *mut leanh::LeanObject,
    mut v___y_5296_: *mut leanh::LeanObject,
    mut v___y_5297_: *mut leanh::LeanObject,
    mut v___y_5298_: *mut leanh::LeanObject,
    mut v___y_5299_: *mut leanh::LeanObject,
    mut v___y_5300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5302_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___redArg(v_cls_5293_, v_msg_5294_, v___y_5297_, v___y_5298_, v___y_5299_, v___y_5300_);
    return v___x_5302_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2___boxed(
    mut v_cls_5303_: *mut leanh::LeanObject,
    mut v_msg_5304_: *mut leanh::LeanObject,
    mut v___y_5305_: *mut leanh::LeanObject,
    mut v___y_5306_: *mut leanh::LeanObject,
    mut v___y_5307_: *mut leanh::LeanObject,
    mut v___y_5308_: *mut leanh::LeanObject,
    mut v___y_5309_: *mut leanh::LeanObject,
    mut v___y_5310_: *mut leanh::LeanObject,
    mut v___y_5311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5312_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2(v_cls_5303_, v_msg_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_);
    leanh::lean_dec(v___y_5310_);
    leanh::lean_dec_ref(v___y_5309_);
    leanh::lean_dec(v___y_5308_);
    leanh::lean_dec_ref(v___y_5307_);
    leanh::lean_dec(v___y_5306_);
    leanh::lean_dec_ref(v___y_5305_);
    return v_res_5312_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(
    mut v_00_u03b2_5313_: *mut leanh::LeanObject,
    mut v_a_5314_: *mut leanh::LeanObject,
    mut v_x_5315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___redArg(v_a_5314_, v_x_5315_);
    return v___x_5316_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_5317_: *mut leanh::LeanObject,
    mut v_a_5318_: *mut leanh::LeanObject,
    mut v_x_5319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5320_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__2_spec__5(v_00_u03b2_5317_, v_a_5318_, v_x_5319_);
    leanh::lean_dec(v_x_5319_);
    leanh::lean_dec(v_a_5318_);
    return v_res_5320_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_5321_: *mut leanh::LeanObject,
    mut v_x_5322_: *mut leanh::LeanObject,
    mut v_x_5323_: usize,
    mut v_x_5324_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5325_: u8 = 0;
    v___x_5325_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___redArg(v_x_5322_, v_x_5323_, v_x_5324_);
    return v___x_5325_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_5326_: *mut leanh::LeanObject,
    mut v_x_5327_: *mut leanh::LeanObject,
    mut v_x_5328_: *mut leanh::LeanObject,
    mut v_x_5329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_11525__boxed_5330_: usize = 0;
    let mut v_res_5331_: u8 = 0;
    let mut v_r_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_11525__boxed_5330_ = leanh::lean_unbox_usize(v_x_5328_);
    leanh::lean_dec(v_x_5328_);
    v_res_5331_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_5326_, v_x_5327_, v_x_11525__boxed_5330_, v_x_5329_);
    leanh::lean_dec_ref(v_x_5329_);
    leanh::lean_dec_ref(v_x_5327_);
    v_r_5332_ = leanh::lean_box((v_res_5331_) as usize);
    return v_r_5332_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(
    mut v_00_u03b2_5333_: *mut leanh::LeanObject,
    mut v_keys_5334_: *mut leanh::LeanObject,
    mut v_vals_5335_: *mut leanh::LeanObject,
    mut v_heq_5336_: *mut leanh::LeanObject,
    mut v_i_5337_: *mut leanh::LeanObject,
    mut v_k_5338_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5339_: u8 = 0;
    v___x_5339_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___redArg(v_keys_5334_, v_i_5337_, v_k_5338_);
    return v___x_5339_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(
    mut v_00_u03b2_5340_: *mut leanh::LeanObject,
    mut v_keys_5341_: *mut leanh::LeanObject,
    mut v_vals_5342_: *mut leanh::LeanObject,
    mut v_heq_5343_: *mut leanh::LeanObject,
    mut v_i_5344_: *mut leanh::LeanObject,
    mut v_k_5345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5346_: u8 = 0;
    let mut v_r_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5346_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__1_spec__4_spec__7(v_00_u03b2_5340_, v_keys_5341_, v_vals_5342_, v_heq_5343_, v_i_5344_, v_k_5345_);
    leanh::lean_dec_ref(v_k_5345_);
    leanh::lean_dec_ref(v_vals_5342_);
    leanh::lean_dec_ref(v_keys_5341_);
    v_r_5347_ = leanh::lean_box((v_res_5346_) as usize);
    return v_r_5347_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(
    mut v_ev_5349_: *mut leanh::LeanObject,
    mut v___x_5350_: *mut leanh::LeanObject,
    mut v___x_5351_: *mut leanh::LeanObject,
    mut v_typeExpr_5352_: *mut leanh::LeanObject,
    mut v_stx_5353_: *mut leanh::LeanObject,
    mut v___y_5354_: *mut leanh::LeanObject,
    mut v___y_5355_: *mut leanh::LeanObject,
    mut v___y_5356_: *mut leanh::LeanObject,
    mut v___y_5357_: *mut leanh::LeanObject,
    mut v___y_5358_: *mut leanh::LeanObject,
    mut v___y_5359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5365_: u8 = 0;
    let mut v_fst_5366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5370_: u8 = 0;
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5382_: u8 = 0;
    let mut v_isSharedCheck_5383_: u8 = 0;
    let mut v_a_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_5359_);
                leanh::lean_inc_ref(v___y_5358_);
                leanh::lean_inc(v___y_5357_);
                leanh::lean_inc_ref(v___y_5356_);
                leanh::lean_inc(v___y_5355_);
                leanh::lean_inc_ref(v___y_5354_);
                v___x_5361_ = leanh::lean_apply_8(
                    v_ev_5349_,
                    v_stx_5353_,
                    v___y_5354_,
                    v___y_5355_,
                    v___y_5356_,
                    v___y_5357_,
                    v___y_5358_,
                    v___y_5359_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_5361_) == 0 {
                    v_a_5362_ = leanh::lean_ctor_get(v___x_5361_, 0);
                    v_isSharedCheck_5383_ = (!leanh::lean_is_exclusive(v___x_5361_)) as u8;
                    if v_isSharedCheck_5383_ == 0 {
                        v___x_5364_ = v___x_5361_;
                        v_isShared_5365_ = v_isSharedCheck_5383_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5362_);
                        leanh::lean_dec(v___x_5361_);
                        v___x_5364_ = leanh::lean_box(0);
                        v_isShared_5365_ = v_isSharedCheck_5383_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_typeExpr_5352_);
                    leanh::lean_dec(v___x_5351_);
                    leanh::lean_dec_ref(v___x_5350_);
                    v_a_5384_ = leanh::lean_ctor_get(v___x_5361_, 0);
                    v_isSharedCheck_5391_ = (!leanh::lean_is_exclusive(v___x_5361_)) as u8;
                    if v_isSharedCheck_5391_ == 0 {
                        v___x_5386_ = v___x_5361_;
                        v_isShared_5387_ = v_isSharedCheck_5391_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5384_);
                        leanh::lean_dec(v___x_5361_);
                        v___x_5386_ = leanh::lean_box(0);
                        v_isShared_5387_ = v_isSharedCheck_5391_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5366_ = leanh::lean_ctor_get(v_a_5362_, 0);
                v_snd_5367_ = leanh::lean_ctor_get(v_a_5362_, 1);
                v_isSharedCheck_5382_ = (!leanh::lean_is_exclusive(v_a_5362_)) as u8;
                if v_isSharedCheck_5382_ == 0 {
                    v___x_5369_ = v_a_5362_;
                    v_isShared_5370_ = v_isSharedCheck_5382_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_5367_);
                    leanh::lean_inc(v_fst_5366_);
                    leanh::lean_dec(v_a_5362_);
                    v___x_5369_ = leanh::lean_box(0);
                    v_isShared_5370_ = v_isSharedCheck_5382_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5371_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5371_, 0, v_fst_5366_);
                v___x_5372_ =
                    l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___closed__0;
                v___x_5373_ = l_Lean_Name_mkStr2(v___x_5350_, v___x_5372_);
                v___x_5374_ = l_Lean_Expr_const___override(v___x_5373_, v___x_5351_);
                v___x_5375_ = l_Lean_mkAppB(v___x_5374_, v_typeExpr_5352_, v_snd_5367_);
                if v_isShared_5370_ == 0 {
                    leanh::lean_ctor_set(v___x_5369_, 1, v___x_5375_);
                    leanh::lean_ctor_set(v___x_5369_, 0, v___x_5371_);
                    v___x_5377_ = v___x_5369_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5381_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5371_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5381_, 1, v___x_5375_);
                    v___x_5377_ = v_reuseFailAlloc_5381_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5365_ == 0 {
                    leanh::lean_ctor_set(v___x_5364_, 0, v___x_5377_);
                    v___x_5379_ = v___x_5364_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5380_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5377_);
                    v___x_5379_ = v_reuseFailAlloc_5380_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5379_;
            }
            5 => {
                if v_isShared_5387_ == 0 {
                    v___x_5389_ = v___x_5386_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5390_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
                    v___x_5389_ = v_reuseFailAlloc_5390_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0___boxed(
    mut v_ev_5392_: *mut leanh::LeanObject,
    mut v___x_5393_: *mut leanh::LeanObject,
    mut v___x_5394_: *mut leanh::LeanObject,
    mut v_typeExpr_5395_: *mut leanh::LeanObject,
    mut v_stx_5396_: *mut leanh::LeanObject,
    mut v___y_5397_: *mut leanh::LeanObject,
    mut v___y_5398_: *mut leanh::LeanObject,
    mut v___y_5399_: *mut leanh::LeanObject,
    mut v___y_5400_: *mut leanh::LeanObject,
    mut v___y_5401_: *mut leanh::LeanObject,
    mut v___y_5402_: *mut leanh::LeanObject,
    mut v___y_5403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5404_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(
        v_ev_5392_,
        v___x_5393_,
        v___x_5394_,
        v_typeExpr_5395_,
        v_stx_5396_,
        v___y_5397_,
        v___y_5398_,
        v___y_5399_,
        v___y_5400_,
        v___y_5401_,
        v___y_5402_,
    );
    leanh::lean_dec(v___y_5402_);
    leanh::lean_dec_ref(v___y_5401_);
    leanh::lean_dec(v___y_5400_);
    leanh::lean_dec_ref(v___y_5399_);
    leanh::lean_dec(v___y_5398_);
    leanh::lean_dec_ref(v___y_5397_);
    return v_res_5404_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5408_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_5409_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1;
    v___x_5410_ = l_Lean_Expr_const___override(v___x_5409_, v___x_5408_);
    return v___x_5410_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5425_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_5426_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8;
    v___x_5427_ = l_Lean_Expr_const___override(v___x_5426_, v___x_5425_);
    return v___x_5427_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(
    mut v_typeExpr_5428_: *mut leanh::LeanObject,
    mut v_ev_5429_: *mut leanh::LeanObject,
    mut v_stx_5430_: *mut leanh::LeanObject,
    mut v_a_5431_: *mut leanh::LeanObject,
    mut v_a_5432_: *mut leanh::LeanObject,
    mut v_a_5433_: *mut leanh::LeanObject,
    mut v_a_5434_: *mut leanh::LeanObject,
    mut v_a_5435_: *mut leanh::LeanObject,
    mut v_a_5436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5449_: u8 = 0;
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: u8 = 0;
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5457_: u8 = 0;
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5461_: u8 = 0;
    let mut v_unused_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5466_: u8 = 0;
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5470_: u8 = 0;
    let mut v___y_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: u8 = 0;
    let mut v_fileName_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5490_: u8 = 0;
    let mut v_cancelTk_x3f_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5492_: u8 = 0;
    let mut v_inheritedTraceOptions_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: u8 = 0;
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: u8 = 0;
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: u8 = 0;
    let mut v___x_5504_: u8 = 0;
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: u8 = 0;
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: u8 = 0;
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: u8 = 0;
    let mut v___x_5518_: u8 = 0;
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: u8 = 0;
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: u8 = 0;
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5438_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__0;
                v___x_5439_ = leanh::lean_unsigned_to_nat(0);
                v___x_5440_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
                );
                v___x_5441_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2,
                );
                leanh::lean_inc_ref(v_typeExpr_5428_);
                v___x_5442_ = l_Lean_Expr_app___override(v___x_5441_, v_typeExpr_5428_);
                v___x_5443_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5443_, 0, v___x_5442_);
                leanh::lean_inc(v_stx_5430_);
                v___x_5475_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_5430_,
                    );
                v___x_5476_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__4;
                v___x_5477_ = l_Lean_Syntax_matchesIdent(v___x_5475_, v___x_5476_);
                if v___x_5477_ == 0 {
                    v_fileName_5478_ = leanh::lean_ctor_get(v_a_5435_, 0);
                    v_fileMap_5479_ = leanh::lean_ctor_get(v_a_5435_, 1);
                    v_options_5480_ = leanh::lean_ctor_get(v_a_5435_, 2);
                    v_currRecDepth_5481_ = leanh::lean_ctor_get(v_a_5435_, 3);
                    v_maxRecDepth_5482_ = leanh::lean_ctor_get(v_a_5435_, 4);
                    v_ref_5483_ = leanh::lean_ctor_get(v_a_5435_, 5);
                    v_currNamespace_5484_ = leanh::lean_ctor_get(v_a_5435_, 6);
                    v_openDecls_5485_ = leanh::lean_ctor_get(v_a_5435_, 7);
                    v_initHeartbeats_5486_ = leanh::lean_ctor_get(v_a_5435_, 8);
                    v_maxHeartbeats_5487_ = leanh::lean_ctor_get(v_a_5435_, 9);
                    v_quotContext_5488_ = leanh::lean_ctor_get(v_a_5435_, 10);
                    v_currMacroScope_5489_ = leanh::lean_ctor_get(v_a_5435_, 11);
                    v_diag_5490_ = leanh::lean_ctor_get_uint8(
                        v_a_5435_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_5491_ = leanh::lean_ctor_get(v_a_5435_, 12);
                    v_suppressElabErrors_5492_ = leanh::lean_ctor_get_uint8(
                        v_a_5435_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_5493_ = leanh::lean_ctor_get(v_a_5435_, 13);
                    v_ref_5494_ = l_Lean_replaceRef(v_stx_5430_, v_ref_5483_);
                    leanh::lean_inc_ref(v_inheritedTraceOptions_5493_);
                    leanh::lean_inc(v_cancelTk_x3f_5491_);
                    leanh::lean_inc(v_currMacroScope_5489_);
                    leanh::lean_inc(v_quotContext_5488_);
                    leanh::lean_inc(v_maxHeartbeats_5487_);
                    leanh::lean_inc(v_initHeartbeats_5486_);
                    leanh::lean_inc(v_openDecls_5485_);
                    leanh::lean_inc(v_currNamespace_5484_);
                    leanh::lean_inc(v_maxRecDepth_5482_);
                    leanh::lean_inc(v_currRecDepth_5481_);
                    leanh::lean_inc_ref(v_options_5480_);
                    leanh::lean_inc_ref(v_fileMap_5479_);
                    leanh::lean_inc_ref(v_fileName_5478_);
                    v___x_5495_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v___x_5495_, 0, v_fileName_5478_);
                    leanh::lean_ctor_set(v___x_5495_, 1, v_fileMap_5479_);
                    leanh::lean_ctor_set(v___x_5495_, 2, v_options_5480_);
                    leanh::lean_ctor_set(v___x_5495_, 3, v_currRecDepth_5481_);
                    leanh::lean_ctor_set(v___x_5495_, 4, v_maxRecDepth_5482_);
                    leanh::lean_ctor_set(v___x_5495_, 5, v_ref_5494_);
                    leanh::lean_ctor_set(v___x_5495_, 6, v_currNamespace_5484_);
                    leanh::lean_ctor_set(v___x_5495_, 7, v_openDecls_5485_);
                    leanh::lean_ctor_set(v___x_5495_, 8, v_initHeartbeats_5486_);
                    leanh::lean_ctor_set(v___x_5495_, 9, v_maxHeartbeats_5487_);
                    leanh::lean_ctor_set(v___x_5495_, 10, v_quotContext_5488_);
                    leanh::lean_ctor_set(v___x_5495_, 11, v_currMacroScope_5489_);
                    leanh::lean_ctor_set(v___x_5495_, 12, v_cancelTk_x3f_5491_);
                    leanh::lean_ctor_set(v___x_5495_, 13, v_inheritedTraceOptions_5493_);
                    leanh::lean_ctor_set_uint8(
                        v___x_5495_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_5490_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_5495_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_5492_,
                    );
                    v___x_5496_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__15;
                    leanh::lean_inc(v___x_5475_);
                    v___x_5497_ = l_Lean_Syntax_isOfKind(v___x_5475_, v___x_5496_);
                    if v___x_5497_ == 0 {
                        v___x_5498_ =
                            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__6;
                        leanh::lean_inc(v___x_5475_);
                        v___x_5499_ = l_Lean_Syntax_isOfKind(v___x_5475_, v___x_5498_);
                        if v___x_5499_ == 0 {
                            v___x_5500_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(
                                    v_ev_5429_,
                                    v___x_5438_,
                                    v___x_5440_,
                                    v_typeExpr_5428_,
                                    v___x_5475_,
                                    v_a_5431_,
                                    v_a_5432_,
                                    v_a_5433_,
                                    v_a_5434_,
                                    v___x_5495_,
                                    v_a_5436_,
                                );
                            leanh::lean_dec_ref_known(v___x_5495_, 14);
                            v___y_5472_ = v___x_5500_;
                            state = 6;
                            continue;
                        } else {
                            v___x_5501_ = l_Lean_Syntax_getArg(v___x_5475_, v___x_5439_);
                            v___x_5502_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__7;
                            v___x_5503_ = l_Lean_Syntax_matchesIdent(v___x_5501_, v___x_5502_);
                            if v___x_5503_ == 0 {
                                leanh::lean_inc(v___x_5501_);
                                v___x_5504_ = l_Lean_Syntax_isOfKind(v___x_5501_, v___x_5496_);
                                if v___x_5504_ == 0 {
                                    leanh::lean_dec(v___x_5501_);
                                    v___x_5505_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v___x_5475_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                    leanh::lean_dec_ref_known(v___x_5495_, 14);
                                    v___y_5472_ = v___x_5505_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_5506_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_5507_ = l_Lean_Syntax_getArg(v___x_5501_, v___x_5506_);
                                    leanh::lean_dec(v___x_5501_);
                                    v___x_5508_ =
                                        l_Lean_Syntax_matchesIdent(v___x_5507_, v___x_5502_);
                                    leanh::lean_dec(v___x_5507_);
                                    if v___x_5508_ == 0 {
                                        v___x_5509_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v___x_5475_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                        leanh::lean_dec_ref_known(v___x_5495_, 14);
                                        v___y_5472_ = v___x_5509_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___x_5510_ =
                                            l_Lean_Syntax_getArg(v___x_5475_, v___x_5506_);
                                        leanh::lean_inc(v___x_5510_);
                                        v___x_5511_ =
                                            l_Lean_Syntax_matchesNull(v___x_5510_, v___x_5506_);
                                        if v___x_5511_ == 0 {
                                            leanh::lean_dec(v___x_5510_);
                                            v___x_5512_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v___x_5475_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                            leanh::lean_dec_ref_known(v___x_5495_, 14);
                                            v___y_5472_ = v___x_5512_;
                                            state = 6;
                                            continue;
                                        } else {
                                            leanh::lean_dec(v___x_5475_);
                                            v_stx_5513_ =
                                                l_Lean_Syntax_getArg(v___x_5510_, v___x_5439_);
                                            leanh::lean_dec(v___x_5510_);
                                            v___x_5514_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v_stx_5513_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                            leanh::lean_dec_ref_known(v___x_5495_, 14);
                                            v___y_5472_ = v___x_5514_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_5515_ = leanh::lean_unsigned_to_nat(1);
                                v___x_5516_ = l_Lean_Syntax_getArg(v___x_5475_, v___x_5515_);
                                leanh::lean_inc(v___x_5516_);
                                v___x_5517_ = l_Lean_Syntax_matchesNull(v___x_5516_, v___x_5515_);
                                if v___x_5517_ == 0 {
                                    leanh::lean_inc(v___x_5501_);
                                    v___x_5518_ = l_Lean_Syntax_isOfKind(v___x_5501_, v___x_5496_);
                                    if v___x_5518_ == 0 {
                                        leanh::lean_dec(v___x_5516_);
                                        leanh::lean_dec(v___x_5501_);
                                        v___x_5519_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v___x_5475_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                        leanh::lean_dec_ref_known(v___x_5495_, 14);
                                        v___y_5472_ = v___x_5519_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v___x_5520_ =
                                            l_Lean_Syntax_getArg(v___x_5501_, v___x_5515_);
                                        leanh::lean_dec(v___x_5501_);
                                        v___x_5521_ =
                                            l_Lean_Syntax_matchesIdent(v___x_5520_, v___x_5502_);
                                        leanh::lean_dec(v___x_5520_);
                                        if v___x_5521_ == 0 {
                                            leanh::lean_dec(v___x_5516_);
                                            v___x_5522_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v___x_5475_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                            leanh::lean_dec_ref_known(v___x_5495_, 14);
                                            v___y_5472_ = v___x_5522_;
                                            state = 6;
                                            continue;
                                        } else {
                                            if v___x_5517_ == 0 {
                                                leanh::lean_dec(v___x_5516_);
                                                v___x_5523_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v___x_5475_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                                leanh::lean_dec_ref_known(v___x_5495_, 14);
                                                v___y_5472_ = v___x_5523_;
                                                state = 6;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v___x_5475_);
                                                v_stx_5524_ =
                                                    l_Lean_Syntax_getArg(v___x_5516_, v___x_5439_);
                                                leanh::lean_dec(v___x_5516_);
                                                v___x_5525_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v_stx_5524_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                                leanh::lean_dec_ref_known(v___x_5495_, 14);
                                                v___y_5472_ = v___x_5525_;
                                                state = 6;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v___x_5501_);
                                    leanh::lean_dec(v___x_5475_);
                                    v_stx_5526_ = l_Lean_Syntax_getArg(v___x_5516_, v___x_5439_);
                                    leanh::lean_dec(v___x_5516_);
                                    v___x_5527_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(v_ev_5429_, v___x_5438_, v___x_5440_, v_typeExpr_5428_, v_stx_5526_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v___x_5495_, v_a_5436_);
                                    leanh::lean_dec_ref_known(v___x_5495_, 14);
                                    v___y_5472_ = v___x_5527_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5528_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5529_ = l_Lean_Syntax_getArg(v___x_5475_, v___x_5528_);
                        v___x_5530_ = l_Lean_Syntax_matchesIdent(v___x_5529_, v___x_5476_);
                        leanh::lean_dec(v___x_5529_);
                        if v___x_5530_ == 0 {
                            v___x_5531_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___lam__0(
                                    v_ev_5429_,
                                    v___x_5438_,
                                    v___x_5440_,
                                    v_typeExpr_5428_,
                                    v___x_5475_,
                                    v_a_5431_,
                                    v_a_5432_,
                                    v_a_5433_,
                                    v_a_5434_,
                                    v___x_5495_,
                                    v_a_5436_,
                                );
                            leanh::lean_dec_ref_known(v___x_5495_, 14);
                            v___y_5472_ = v___x_5531_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v___x_5495_, 14);
                            leanh::lean_dec(v___x_5475_);
                            leanh::lean_dec_ref(v_ev_5429_);
                            v___x_5532_ = leanh::lean_box(0);
                            v___x_5533_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once), _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9);
                            v___x_5534_ = l_Lean_Expr_app___override(v___x_5533_, v_typeExpr_5428_);
                            leanh::lean_inc_ref(v___x_5534_);
                            v___x_5535_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5535_, 0, v___x_5532_);
                            leanh::lean_ctor_set(v___x_5535_, 1, v___x_5534_);
                            v_a_5445_ = v___x_5535_;
                            v_snd_5446_ = v___x_5534_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5475_);
                    leanh::lean_dec_ref(v_ev_5429_);
                    v___x_5536_ = leanh::lean_box(0);
                    v___x_5537_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__9,
                    );
                    v___x_5538_ = l_Lean_Expr_app___override(v___x_5537_, v_typeExpr_5428_);
                    leanh::lean_inc_ref(v___x_5538_);
                    v___x_5539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5539_, 0, v___x_5536_);
                    leanh::lean_ctor_set(v___x_5539_, 1, v___x_5538_);
                    v_a_5445_ = v___x_5539_;
                    v_snd_5446_ = v___x_5538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5447_ = lean_st_ref_get(v_a_5436_);
                v_infoState_5448_ = leanh::lean_ctor_get(v___x_5447_, 7);
                leanh::lean_inc_ref(v_infoState_5448_);
                leanh::lean_dec(v___x_5447_);
                v_enabled_5449_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5448_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5448_);
                if v_enabled_5449_ == 0 {
                    leanh::lean_dec_ref(v_snd_5446_);
                    leanh::lean_dec_ref_known(v___x_5443_, 1);
                    leanh::lean_dec(v_stx_5430_);
                    v___x_5450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5450_, 0, v_a_5445_);
                    return v___x_5450_;
                } else {
                    v___x_5451_ = leanh::lean_box(0);
                    v___x_5452_ = leanh::lean_box(0);
                    v___x_5453_ = 0;
                    v___x_5454_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_5430_,
                        v_snd_5446_,
                        v___x_5443_,
                        v___x_5451_,
                        v___x_5452_,
                        v___x_5453_,
                        v___x_5453_,
                        v_a_5431_,
                        v_a_5432_,
                        v_a_5433_,
                        v_a_5434_,
                        v_a_5435_,
                        v_a_5436_,
                    );
                    if leanh::lean_obj_tag(v___x_5454_) == 0 {
                        v_isSharedCheck_5461_ =
                            (!leanh::lean_is_exclusive(v___x_5454_)) as u8;
                        if v_isSharedCheck_5461_ == 0 {
                            v_unused_5462_ = leanh::lean_ctor_get(v___x_5454_, 0);
                            leanh::lean_dec(v_unused_5462_);
                            v___x_5456_ = v___x_5454_;
                            v_isShared_5457_ = v_isSharedCheck_5461_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5454_);
                            v___x_5456_ = leanh::lean_box(0);
                            v_isShared_5457_ = v_isSharedCheck_5461_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_5445_);
                        v_a_5463_ = leanh::lean_ctor_get(v___x_5454_, 0);
                        v_isSharedCheck_5470_ =
                            (!leanh::lean_is_exclusive(v___x_5454_)) as u8;
                        if v_isSharedCheck_5470_ == 0 {
                            v___x_5465_ = v___x_5454_;
                            v_isShared_5466_ = v_isSharedCheck_5470_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5463_);
                            leanh::lean_dec(v___x_5454_);
                            v___x_5465_ = leanh::lean_box(0);
                            v_isShared_5466_ = v_isSharedCheck_5470_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5457_ == 0 {
                    leanh::lean_ctor_set(v___x_5456_, 0, v_a_5445_);
                    v___x_5459_ = v___x_5456_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5460_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_a_5445_);
                    v___x_5459_ = v_reuseFailAlloc_5460_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5459_;
            }
            4 => {
                if v_isShared_5466_ == 0 {
                    v___x_5468_ = v___x_5465_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
                    v___x_5468_ = v_reuseFailAlloc_5469_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5468_;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_5472_) == 0 {
                    v_a_5473_ = leanh::lean_ctor_get(v___y_5472_, 0);
                    leanh::lean_inc(v_a_5473_);
                    leanh::lean_dec_ref_known(v___y_5472_, 1);
                    v_snd_5474_ = leanh::lean_ctor_get(v_a_5473_, 1);
                    leanh::lean_inc(v_snd_5474_);
                    v_a_5445_ = v_a_5473_;
                    v_snd_5446_ = v_snd_5474_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_5443_, 1);
                    leanh::lean_dec(v_stx_5430_);
                    return v___y_5472_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___boxed(
    mut v_typeExpr_5540_: *mut leanh::LeanObject,
    mut v_ev_5541_: *mut leanh::LeanObject,
    mut v_stx_5542_: *mut leanh::LeanObject,
    mut v_a_5543_: *mut leanh::LeanObject,
    mut v_a_5544_: *mut leanh::LeanObject,
    mut v_a_5545_: *mut leanh::LeanObject,
    mut v_a_5546_: *mut leanh::LeanObject,
    mut v_a_5547_: *mut leanh::LeanObject,
    mut v_a_5548_: *mut leanh::LeanObject,
    mut v_a_5549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5550_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(
        v_typeExpr_5540_,
        v_ev_5541_,
        v_stx_5542_,
        v_a_5543_,
        v_a_5544_,
        v_a_5545_,
        v_a_5546_,
        v_a_5547_,
        v_a_5548_,
    );
    leanh::lean_dec(v_a_5548_);
    leanh::lean_dec_ref(v_a_5547_);
    leanh::lean_dec(v_a_5546_);
    leanh::lean_dec_ref(v_a_5545_);
    leanh::lean_dec(v_a_5544_);
    leanh::lean_dec_ref(v_a_5543_);
    return v_res_5550_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(
    mut v_00_u03b1_5551_: *mut leanh::LeanObject,
    mut v_typeExpr_5552_: *mut leanh::LeanObject,
    mut v_ev_5553_: *mut leanh::LeanObject,
    mut v_stx_5554_: *mut leanh::LeanObject,
    mut v_a_5555_: *mut leanh::LeanObject,
    mut v_a_5556_: *mut leanh::LeanObject,
    mut v_a_5557_: *mut leanh::LeanObject,
    mut v_a_5558_: *mut leanh::LeanObject,
    mut v_a_5559_: *mut leanh::LeanObject,
    mut v_a_5560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5562_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg(
        v_typeExpr_5552_,
        v_ev_5553_,
        v_stx_5554_,
        v_a_5555_,
        v_a_5556_,
        v_a_5557_,
        v_a_5558_,
        v_a_5559_,
        v_a_5560_,
    );
    return v___x_5562_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed(
    mut v_00_u03b1_5563_: *mut leanh::LeanObject,
    mut v_typeExpr_5564_: *mut leanh::LeanObject,
    mut v_ev_5565_: *mut leanh::LeanObject,
    mut v_stx_5566_: *mut leanh::LeanObject,
    mut v_a_5567_: *mut leanh::LeanObject,
    mut v_a_5568_: *mut leanh::LeanObject,
    mut v_a_5569_: *mut leanh::LeanObject,
    mut v_a_5570_: *mut leanh::LeanObject,
    mut v_a_5571_: *mut leanh::LeanObject,
    mut v_a_5572_: *mut leanh::LeanObject,
    mut v_a_5573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5574_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx(
        v_00_u03b1_5563_,
        v_typeExpr_5564_,
        v_ev_5565_,
        v_stx_5566_,
        v_a_5567_,
        v_a_5568_,
        v_a_5569_,
        v_a_5570_,
        v_a_5571_,
        v_a_5572_,
    );
    leanh::lean_dec(v_a_5572_);
    leanh::lean_dec_ref(v_a_5571_);
    leanh::lean_dec(v_a_5570_);
    leanh::lean_dec_ref(v_a_5569_);
    leanh::lean_dec(v_a_5568_);
    leanh::lean_dec_ref(v_a_5567_);
    return v_res_5574_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(
    mut v___x_5575_: u8,
    mut v_as_5576_: *mut leanh::LeanObject,
    mut v_i_5577_: usize,
    mut v_stop_5578_: usize,
    mut v_b_5579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: usize = 0;
    let mut v___x_5583_: usize = 0;
    let mut v___x_5585_: u8 = 0;
    let mut v_fst_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: u8 = 0;
    let mut v_snd_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5596_: u8 = 0;
    let mut v_unused_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5601_: u8 = 0;
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5608_: u8 = 0;
    let mut v_unused_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5585_ = lean_usize_dec_eq(v_i_5577_, v_stop_5578_);
                if v___x_5585_ == 0 {
                    v_fst_5586_ = leanh::lean_ctor_get(v_b_5579_, 0);
                    v___x_5587_ = (leanh::lean_unbox(v_fst_5586_) as u8);
                    if v___x_5587_ == 0 {
                        v_snd_5588_ = leanh::lean_ctor_get(v_b_5579_, 1);
                        v_isSharedCheck_5596_ = (!leanh::lean_is_exclusive(v_b_5579_)) as u8;
                        if v_isSharedCheck_5596_ == 0 {
                            v_unused_5597_ = leanh::lean_ctor_get(v_b_5579_, 0);
                            leanh::lean_dec(v_unused_5597_);
                            v___x_5590_ = v_b_5579_;
                            v_isShared_5591_ = v_isSharedCheck_5596_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_5588_);
                            leanh::lean_dec(v_b_5579_);
                            v___x_5590_ = leanh::lean_box(0);
                            v_isShared_5591_ = v_isSharedCheck_5596_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_5598_ = leanh::lean_ctor_get(v_b_5579_, 1);
                        v_isSharedCheck_5608_ = (!leanh::lean_is_exclusive(v_b_5579_)) as u8;
                        if v_isSharedCheck_5608_ == 0 {
                            v_unused_5609_ = leanh::lean_ctor_get(v_b_5579_, 0);
                            leanh::lean_dec(v_unused_5609_);
                            v___x_5600_ = v_b_5579_;
                            v_isShared_5601_ = v_isSharedCheck_5608_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_5598_);
                            leanh::lean_dec(v_b_5579_);
                            v___x_5600_ = leanh::lean_box(0);
                            v_isShared_5601_ = v_isSharedCheck_5608_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_5579_;
                }
            }
            1 => {
                v___x_5582_ = 1usize;
                v___x_5583_ = lean_usize_add(v_i_5577_, v___x_5582_);
                v_i_5577_ = v___x_5583_;
                v_b_5579_ = v___y_5581_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5592_ = leanh::lean_box((v___x_5575_) as usize);
                if v_isShared_5591_ == 0 {
                    leanh::lean_ctor_set(v___x_5590_, 0, v___x_5592_);
                    v___x_5594_ = v___x_5590_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5595_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5595_, 1, v_snd_5588_);
                    v___x_5594_ = v_reuseFailAlloc_5595_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5581_ = v___x_5594_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5602_ = lean_array_uget_borrowed(v_as_5576_, v_i_5577_);
                leanh::lean_inc(v___x_5602_);
                v___x_5603_ = lean_array_push(v_snd_5598_, v___x_5602_);
                v___x_5604_ = leanh::lean_box((v___x_5585_) as usize);
                if v_isShared_5601_ == 0 {
                    leanh::lean_ctor_set(v___x_5600_, 1, v___x_5603_);
                    leanh::lean_ctor_set(v___x_5600_, 0, v___x_5604_);
                    v___x_5606_ = v___x_5600_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5604_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5607_, 1, v___x_5603_);
                    v___x_5606_ = v_reuseFailAlloc_5607_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5581_ = v___x_5606_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3___boxed(
    mut v___x_5610_: *mut leanh::LeanObject,
    mut v_as_5611_: *mut leanh::LeanObject,
    mut v_i_5612_: *mut leanh::LeanObject,
    mut v_stop_5613_: *mut leanh::LeanObject,
    mut v_b_5614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1661__boxed_5615_: u8 = 0;
    let mut v_i_boxed_5616_: usize = 0;
    let mut v_stop_boxed_5617_: usize = 0;
    let mut v_res_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1661__boxed_5615_ = (leanh::lean_unbox(v___x_5610_) as u8);
    v_i_boxed_5616_ = leanh::lean_unbox_usize(v_i_5612_);
    leanh::lean_dec(v_i_5612_);
    v_stop_boxed_5617_ = leanh::lean_unbox_usize(v_stop_5613_);
    leanh::lean_dec(v_stop_5613_);
    v_res_5618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_1661__boxed_5615_, v_as_5611_, v_i_boxed_5616_, v_stop_boxed_5617_, v_b_5614_);
    leanh::lean_dec_ref(v_as_5611_);
    return v_res_5618_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(
    mut v_ev_5619_: *mut leanh::LeanObject,
    mut v_sz_5620_: usize,
    mut v_i_5621_: usize,
    mut v_bs_5622_: *mut leanh::LeanObject,
    mut v___y_5623_: *mut leanh::LeanObject,
    mut v___y_5624_: *mut leanh::LeanObject,
    mut v___y_5625_: *mut leanh::LeanObject,
    mut v___y_5626_: *mut leanh::LeanObject,
    mut v___y_5627_: *mut leanh::LeanObject,
    mut v___y_5628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5630_: u8 = 0;
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: usize = 0;
    let mut v___x_5638_: usize = 0;
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5644_: u8 = 0;
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5630_ = lean_usize_dec_lt(v_i_5621_, v_sz_5620_);
                if v___x_5630_ == 0 {
                    leanh::lean_dec_ref(v_ev_5619_);
                    v___x_5631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5631_, 0, v_bs_5622_);
                    return v___x_5631_;
                } else {
                    v_v_5632_ = lean_array_uget_borrowed(v_bs_5622_, v_i_5621_);
                    leanh::lean_inc_ref(v_ev_5619_);
                    leanh::lean_inc(v___y_5628_);
                    leanh::lean_inc_ref(v___y_5627_);
                    leanh::lean_inc(v___y_5626_);
                    leanh::lean_inc_ref(v___y_5625_);
                    leanh::lean_inc(v___y_5624_);
                    leanh::lean_inc_ref(v___y_5623_);
                    leanh::lean_inc(v_v_5632_);
                    v___x_5633_ = leanh::lean_apply_8(
                        v_ev_5619_,
                        v_v_5632_,
                        v___y_5623_,
                        v___y_5624_,
                        v___y_5625_,
                        v___y_5626_,
                        v___y_5627_,
                        v___y_5628_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_5633_) == 0 {
                        v_a_5634_ = leanh::lean_ctor_get(v___x_5633_, 0);
                        leanh::lean_inc(v_a_5634_);
                        leanh::lean_dec_ref_known(v___x_5633_, 1);
                        v___x_5635_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5636_ = lean_array_uset(v_bs_5622_, v_i_5621_, v___x_5635_);
                        v___x_5637_ = 1usize;
                        v___x_5638_ = lean_usize_add(v_i_5621_, v___x_5637_);
                        v___x_5639_ = lean_array_uset(v_bs_x27_5636_, v_i_5621_, v_a_5634_);
                        v_i_5621_ = v___x_5638_;
                        v_bs_5622_ = v___x_5639_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_5622_);
                        leanh::lean_dec_ref(v_ev_5619_);
                        v_a_5641_ = leanh::lean_ctor_get(v___x_5633_, 0);
                        v_isSharedCheck_5648_ =
                            (!leanh::lean_is_exclusive(v___x_5633_)) as u8;
                        if v_isSharedCheck_5648_ == 0 {
                            v___x_5643_ = v___x_5633_;
                            v_isShared_5644_ = v_isSharedCheck_5648_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5641_);
                            leanh::lean_dec(v___x_5633_);
                            v___x_5643_ = leanh::lean_box(0);
                            v_isShared_5644_ = v_isSharedCheck_5648_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5644_ == 0 {
                    v___x_5646_ = v___x_5643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5647_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5641_);
                    v___x_5646_ = v_reuseFailAlloc_5647_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg___boxed(
    mut v_ev_5649_: *mut leanh::LeanObject,
    mut v_sz_5650_: *mut leanh::LeanObject,
    mut v_i_5651_: *mut leanh::LeanObject,
    mut v_bs_5652_: *mut leanh::LeanObject,
    mut v___y_5653_: *mut leanh::LeanObject,
    mut v___y_5654_: *mut leanh::LeanObject,
    mut v___y_5655_: *mut leanh::LeanObject,
    mut v___y_5656_: *mut leanh::LeanObject,
    mut v___y_5657_: *mut leanh::LeanObject,
    mut v___y_5658_: *mut leanh::LeanObject,
    mut v___y_5659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5660_: usize = 0;
    let mut v_i_boxed_5661_: usize = 0;
    let mut v_res_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5660_ = leanh::lean_unbox_usize(v_sz_5650_);
    leanh::lean_dec(v_sz_5650_);
    v_i_boxed_5661_ = leanh::lean_unbox_usize(v_i_5651_);
    leanh::lean_dec(v_i_5651_);
    v_res_5662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_5649_, v_sz_boxed_5660_, v_i_boxed_5661_, v_bs_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
    leanh::lean_dec(v___y_5658_);
    leanh::lean_dec_ref(v___y_5657_);
    leanh::lean_dec(v___y_5656_);
    leanh::lean_dec_ref(v___y_5655_);
    leanh::lean_dec(v___y_5654_);
    leanh::lean_dec_ref(v___y_5653_);
    return v_res_5662_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5668_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_5669_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2;
    v___x_5670_ = l_Lean_Expr_const___override(v___x_5669_, v___x_5668_);
    return v___x_5670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(
    mut v_typeExpr_5671_: *mut leanh::LeanObject,
    mut v_as_5672_: *mut leanh::LeanObject,
    mut v_i_5673_: usize,
    mut v_stop_5674_: usize,
    mut v_b_5675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5676_: u8 = 0;
    let mut v___x_5677_: usize = 0;
    let mut v___x_5678_: usize = 0;
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5676_ = lean_usize_dec_eq(v_i_5673_, v_stop_5674_);
                if v___x_5676_ == 0 {
                    v___x_5677_ = 1usize;
                    v___x_5678_ = lean_usize_sub(v_i_5673_, v___x_5677_);
                    v___x_5679_ = lean_array_uget_borrowed(v_as_5672_, v___x_5678_);
                    v___x_5680_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
                    leanh::lean_inc(v___x_5679_);
                    leanh::lean_inc_ref(v_typeExpr_5671_);
                    v___x_5681_ =
                        l_Lean_mkApp3(v___x_5680_, v_typeExpr_5671_, v___x_5679_, v_b_5675_);
                    v_i_5673_ = v___x_5678_;
                    v_b_5675_ = v___x_5681_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_typeExpr_5671_);
                    return v_b_5675_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___boxed(
    mut v_typeExpr_5683_: *mut leanh::LeanObject,
    mut v_as_5684_: *mut leanh::LeanObject,
    mut v_i_5685_: *mut leanh::LeanObject,
    mut v_stop_5686_: *mut leanh::LeanObject,
    mut v_b_5687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5688_: usize = 0;
    let mut v_stop_boxed_5689_: usize = 0;
    let mut v_res_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5688_ = leanh::lean_unbox_usize(v_i_5685_);
    leanh::lean_dec(v_i_5685_);
    v_stop_boxed_5689_ = leanh::lean_unbox_usize(v_stop_5686_);
    leanh::lean_dec(v_stop_5686_);
    v_res_5690_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_5683_, v_as_5684_, v_i_boxed_5688_, v_stop_boxed_5689_, v_b_5687_);
    leanh::lean_dec_ref(v_as_5684_);
    return v_res_5690_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(
    mut v_sz_5691_: usize,
    mut v_i_5692_: usize,
    mut v_bs_5693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5694_: u8 = 0;
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: usize = 0;
    let mut v___x_5700_: usize = 0;
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5694_ = lean_usize_dec_lt(v_i_5692_, v_sz_5691_);
                if v___x_5694_ == 0 {
                    v___x_5695_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5695_, 0, v_bs_5693_);
                    return v___x_5695_;
                } else {
                    v_v_5696_ = lean_array_uget(v_bs_5693_, v_i_5692_);
                    v___x_5697_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5698_ = lean_array_uset(v_bs_5693_, v_i_5692_, v___x_5697_);
                    v___x_5699_ = 1usize;
                    v___x_5700_ = lean_usize_add(v_i_5692_, v___x_5699_);
                    v___x_5701_ = lean_array_uset(v_bs_x27_5698_, v_i_5692_, v_v_5696_);
                    v_i_5692_ = v___x_5700_;
                    v_bs_5693_ = v___x_5701_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0___boxed(
    mut v_sz_5703_: *mut leanh::LeanObject,
    mut v_i_5704_: *mut leanh::LeanObject,
    mut v_bs_5705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5706_: usize = 0;
    let mut v_i_boxed_5707_: usize = 0;
    let mut v_res_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5706_ = leanh::lean_unbox_usize(v_sz_5703_);
    leanh::lean_dec(v_sz_5703_);
    v_i_boxed_5707_ = leanh::lean_unbox_usize(v_i_5704_);
    leanh::lean_dec(v_i_5704_);
    v_res_5708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_boxed_5706_, v_i_boxed_5707_, v_bs_5705_);
    return v_res_5708_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5711_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_5712_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0;
    v___x_5713_ = l_Lean_Expr_const___override(v___x_5712_, v___x_5711_);
    return v___x_5713_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5721_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_5722_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5;
    v___x_5723_ = l_Lean_Expr_const___override(v___x_5722_, v___x_5721_);
    return v___x_5723_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(
    mut v_typeExpr_5726_: *mut leanh::LeanObject,
    mut v_ev_5727_: *mut leanh::LeanObject,
    mut v_stx_5728_: *mut leanh::LeanObject,
    mut v_a_5729_: *mut leanh::LeanObject,
    mut v_a_5730_: *mut leanh::LeanObject,
    mut v_a_5731_: *mut leanh::LeanObject,
    mut v_a_5732_: *mut leanh::LeanObject,
    mut v_a_5733_: *mut leanh::LeanObject,
    mut v_a_5734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5748_: u8 = 0;
    let mut v_cancelTk_x3f_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5750_: u8 = 0;
    let mut v_inheritedTraceOptions_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5761_: u8 = 0;
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: u8 = 0;
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5769_: u8 = 0;
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5773_: u8 = 0;
    let mut v_unused_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5778_: u8 = 0;
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5782_: u8 = 0;
    let mut v___y_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: u8 = 0;
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5798_: usize = 0;
    let mut v___x_5799_: usize = 0;
    let mut v___x_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5803_: usize = 0;
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: u8 = 0;
    let mut v___x_5813_: usize = 0;
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5818_: u8 = 0;
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5822_: u8 = 0;
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: u8 = 0;
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: u8 = 0;
    let mut v___x_5832_: usize = 0;
    let mut v___x_5833_: usize = 0;
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: usize = 0;
    let mut v___x_5837_: usize = 0;
    let mut v___x_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5736_ = leanh::lean_ctor_get(v_a_5733_, 0);
                v_fileMap_5737_ = leanh::lean_ctor_get(v_a_5733_, 1);
                v_options_5738_ = leanh::lean_ctor_get(v_a_5733_, 2);
                v_currRecDepth_5739_ = leanh::lean_ctor_get(v_a_5733_, 3);
                v_maxRecDepth_5740_ = leanh::lean_ctor_get(v_a_5733_, 4);
                v_ref_5741_ = leanh::lean_ctor_get(v_a_5733_, 5);
                v_currNamespace_5742_ = leanh::lean_ctor_get(v_a_5733_, 6);
                v_openDecls_5743_ = leanh::lean_ctor_get(v_a_5733_, 7);
                v_initHeartbeats_5744_ = leanh::lean_ctor_get(v_a_5733_, 8);
                v_maxHeartbeats_5745_ = leanh::lean_ctor_get(v_a_5733_, 9);
                v_quotContext_5746_ = leanh::lean_ctor_get(v_a_5733_, 10);
                v_currMacroScope_5747_ = leanh::lean_ctor_get(v_a_5733_, 11);
                v_diag_5748_ = leanh::lean_ctor_get_uint8(
                    v_a_5733_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5749_ = leanh::lean_ctor_get(v_a_5733_, 12);
                v_suppressElabErrors_5750_ = leanh::lean_ctor_get_uint8(
                    v_a_5733_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5751_ = leanh::lean_ctor_get(v_a_5733_, 13);
                v___x_5752_ = leanh::lean_unsigned_to_nat(0);
                v___x_5753_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1,
                );
                leanh::lean_inc_ref(v_typeExpr_5726_);
                v___x_5754_ = l_Lean_Expr_app___override(v___x_5753_, v_typeExpr_5726_);
                v___x_5755_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5755_, 0, v___x_5754_);
                leanh::lean_inc(v_stx_5728_);
                v___x_5790_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_5728_,
                    );
                v___x_5791_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__3;
                leanh::lean_inc(v___x_5790_);
                v___x_5792_ = l_Lean_Syntax_isOfKind(v___x_5790_, v___x_5791_);
                if v___x_5792_ == 0 {
                    leanh::lean_dec(v___x_5790_);
                    leanh::lean_dec_ref_known(v___x_5755_, 1);
                    leanh::lean_dec(v_stx_5728_);
                    leanh::lean_dec_ref(v_ev_5727_);
                    leanh::lean_dec_ref(v_typeExpr_5726_);
                    v___x_5793_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                    v___y_5789_ = v___x_5793_;
                    state = 7;
                    continue;
                } else {
                    v_ref_5794_ = l_Lean_replaceRef(v_stx_5728_, v_ref_5741_);
                    leanh::lean_inc_ref(v_inheritedTraceOptions_5751_);
                    leanh::lean_inc(v_cancelTk_x3f_5749_);
                    leanh::lean_inc(v_currMacroScope_5747_);
                    leanh::lean_inc(v_quotContext_5746_);
                    leanh::lean_inc(v_maxHeartbeats_5745_);
                    leanh::lean_inc(v_initHeartbeats_5744_);
                    leanh::lean_inc(v_openDecls_5743_);
                    leanh::lean_inc(v_currNamespace_5742_);
                    leanh::lean_inc(v_maxRecDepth_5740_);
                    leanh::lean_inc(v_currRecDepth_5739_);
                    leanh::lean_inc_ref(v_options_5738_);
                    leanh::lean_inc_ref(v_fileMap_5737_);
                    leanh::lean_inc_ref(v_fileName_5736_);
                    v___x_5795_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v___x_5795_, 0, v_fileName_5736_);
                    leanh::lean_ctor_set(v___x_5795_, 1, v_fileMap_5737_);
                    leanh::lean_ctor_set(v___x_5795_, 2, v_options_5738_);
                    leanh::lean_ctor_set(v___x_5795_, 3, v_currRecDepth_5739_);
                    leanh::lean_ctor_set(v___x_5795_, 4, v_maxRecDepth_5740_);
                    leanh::lean_ctor_set(v___x_5795_, 5, v_ref_5794_);
                    leanh::lean_ctor_set(v___x_5795_, 6, v_currNamespace_5742_);
                    leanh::lean_ctor_set(v___x_5795_, 7, v_openDecls_5743_);
                    leanh::lean_ctor_set(v___x_5795_, 8, v_initHeartbeats_5744_);
                    leanh::lean_ctor_set(v___x_5795_, 9, v_maxHeartbeats_5745_);
                    leanh::lean_ctor_set(v___x_5795_, 10, v_quotContext_5746_);
                    leanh::lean_ctor_set(v___x_5795_, 11, v_currMacroScope_5747_);
                    leanh::lean_ctor_set(v___x_5795_, 12, v_cancelTk_x3f_5749_);
                    leanh::lean_ctor_set(v___x_5795_, 13, v_inheritedTraceOptions_5751_);
                    leanh::lean_ctor_set_uint8(
                        v___x_5795_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_5748_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_5795_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_5750_,
                    );
                    v___x_5823_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5824_ = l_Lean_Syntax_getArg(v___x_5790_, v___x_5823_);
                    leanh::lean_dec(v___x_5790_);
                    v___x_5825_ = l_Lean_Syntax_getArgs(v___x_5824_);
                    leanh::lean_dec(v___x_5824_);
                    v___x_5826_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7;
                    v___x_5827_ = lean_array_get_size(v___x_5825_);
                    v___x_5828_ = lean_nat_dec_lt(v___x_5752_, v___x_5827_);
                    if v___x_5828_ == 0 {
                        leanh::lean_dec_ref(v___x_5825_);
                        v___y_5797_ = v___x_5826_;
                        state = 8;
                        continue;
                    } else {
                        v___x_5829_ = leanh::lean_box((v___x_5792_) as usize);
                        v___x_5830_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5830_, 0, v___x_5829_);
                        leanh::lean_ctor_set(v___x_5830_, 1, v___x_5826_);
                        v___x_5831_ = lean_nat_dec_le(v___x_5827_, v___x_5827_);
                        if v___x_5831_ == 0 {
                            if v___x_5828_ == 0 {
                                leanh::lean_dec_ref_known(v___x_5830_, 2);
                                leanh::lean_dec_ref(v___x_5825_);
                                v___y_5797_ = v___x_5826_;
                                state = 8;
                                continue;
                            } else {
                                v___x_5832_ = 0usize;
                                v___x_5833_ = lean_usize_of_nat(v___x_5827_);
                                v___x_5834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_5792_, v___x_5825_, v___x_5832_, v___x_5833_, v___x_5830_);
                                leanh::lean_dec_ref(v___x_5825_);
                                v_snd_5835_ = leanh::lean_ctor_get(v___x_5834_, 1);
                                leanh::lean_inc(v_snd_5835_);
                                leanh::lean_dec_ref(v___x_5834_);
                                v___y_5797_ = v_snd_5835_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_5836_ = 0usize;
                            v___x_5837_ = lean_usize_of_nat(v___x_5827_);
                            v___x_5838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_5792_, v___x_5825_, v___x_5836_, v___x_5837_, v___x_5830_);
                            leanh::lean_dec_ref(v___x_5825_);
                            v_snd_5839_ = leanh::lean_ctor_get(v___x_5838_, 1);
                            leanh::lean_inc(v_snd_5839_);
                            leanh::lean_dec_ref(v___x_5838_);
                            v___y_5797_ = v_snd_5839_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5759_ = lean_st_ref_get(v_a_5734_);
                v_infoState_5760_ = leanh::lean_ctor_get(v___x_5759_, 7);
                leanh::lean_inc_ref(v_infoState_5760_);
                leanh::lean_dec(v___x_5759_);
                v_enabled_5761_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5760_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5760_);
                if v_enabled_5761_ == 0 {
                    leanh::lean_dec_ref(v_snd_5758_);
                    leanh::lean_dec_ref_known(v___x_5755_, 1);
                    leanh::lean_dec(v_stx_5728_);
                    v___x_5762_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5762_, 0, v_a_5757_);
                    return v___x_5762_;
                } else {
                    v___x_5763_ = leanh::lean_box(0);
                    v___x_5764_ = leanh::lean_box(0);
                    v___x_5765_ = 0;
                    v___x_5766_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_5728_,
                        v_snd_5758_,
                        v___x_5755_,
                        v___x_5763_,
                        v___x_5764_,
                        v___x_5765_,
                        v___x_5765_,
                        v_a_5729_,
                        v_a_5730_,
                        v_a_5731_,
                        v_a_5732_,
                        v_a_5733_,
                        v_a_5734_,
                    );
                    if leanh::lean_obj_tag(v___x_5766_) == 0 {
                        v_isSharedCheck_5773_ =
                            (!leanh::lean_is_exclusive(v___x_5766_)) as u8;
                        if v_isSharedCheck_5773_ == 0 {
                            v_unused_5774_ = leanh::lean_ctor_get(v___x_5766_, 0);
                            leanh::lean_dec(v_unused_5774_);
                            v___x_5768_ = v___x_5766_;
                            v_isShared_5769_ = v_isSharedCheck_5773_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5766_);
                            v___x_5768_ = leanh::lean_box(0);
                            v_isShared_5769_ = v_isSharedCheck_5773_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_5757_);
                        v_a_5775_ = leanh::lean_ctor_get(v___x_5766_, 0);
                        v_isSharedCheck_5782_ =
                            (!leanh::lean_is_exclusive(v___x_5766_)) as u8;
                        if v_isSharedCheck_5782_ == 0 {
                            v___x_5777_ = v___x_5766_;
                            v_isShared_5778_ = v_isSharedCheck_5782_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5775_);
                            leanh::lean_dec(v___x_5766_);
                            v___x_5777_ = leanh::lean_box(0);
                            v_isShared_5778_ = v_isSharedCheck_5782_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5769_ == 0 {
                    leanh::lean_ctor_set(v___x_5768_, 0, v_a_5757_);
                    v___x_5771_ = v___x_5768_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5772_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5772_, 0, v_a_5757_);
                    v___x_5771_ = v_reuseFailAlloc_5772_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5771_;
            }
            4 => {
                if v_isShared_5778_ == 0 {
                    v___x_5780_ = v___x_5777_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
                    v___x_5780_ = v_reuseFailAlloc_5781_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5780_;
            }
            6 => {
                v___x_5786_ = lean_array_to_list(v___y_5784_);
                leanh::lean_inc_ref(v___y_5785_);
                v___x_5787_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5787_, 0, v___x_5786_);
                leanh::lean_ctor_set(v___x_5787_, 1, v___y_5785_);
                v_a_5757_ = v___x_5787_;
                v_snd_5758_ = v___y_5785_;
                state = 1;
                continue;
            }
            7 => {
                return v___y_5789_;
            }
            8 => {
                v_sz_5798_ = lean_array_size(v___y_5797_);
                v___x_5799_ = 0usize;
                v___x_5800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_5798_, v___x_5799_, v___y_5797_);
                if leanh::lean_obj_tag(v___x_5800_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5795_, 14);
                    leanh::lean_dec_ref_known(v___x_5755_, 1);
                    leanh::lean_dec(v_stx_5728_);
                    leanh::lean_dec_ref(v_ev_5727_);
                    leanh::lean_dec_ref(v_typeExpr_5726_);
                    v___x_5801_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                    v___y_5789_ = v___x_5801_;
                    state = 7;
                    continue;
                } else {
                    v_val_5802_ = leanh::lean_ctor_get(v___x_5800_, 0);
                    leanh::lean_inc(v_val_5802_);
                    leanh::lean_dec_ref_known(v___x_5800_, 1);
                    v_sz_5803_ = lean_array_size(v_val_5802_);
                    v___x_5804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_5727_, v_sz_5803_, v___x_5799_, v_val_5802_, v_a_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v___x_5795_, v_a_5734_);
                    leanh::lean_dec_ref_known(v___x_5795_, 14);
                    if leanh::lean_obj_tag(v___x_5804_) == 0 {
                        v_a_5805_ = leanh::lean_ctor_get(v___x_5804_, 0);
                        leanh::lean_inc(v_a_5805_);
                        leanh::lean_dec_ref_known(v___x_5804_, 1);
                        v___x_5806_ = l_Array_unzip___redArg(v_a_5805_);
                        leanh::lean_dec(v_a_5805_);
                        v_fst_5807_ = leanh::lean_ctor_get(v___x_5806_, 0);
                        leanh::lean_inc(v_fst_5807_);
                        v_snd_5808_ = leanh::lean_ctor_get(v___x_5806_, 1);
                        leanh::lean_inc(v_snd_5808_);
                        leanh::lean_dec_ref(v___x_5806_);
                        v___x_5809_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once), _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
                        leanh::lean_inc_ref(v_typeExpr_5726_);
                        v___x_5810_ = l_Lean_Expr_app___override(v___x_5809_, v_typeExpr_5726_);
                        v___x_5811_ = lean_array_get_size(v_snd_5808_);
                        v___x_5812_ = lean_nat_dec_lt(v___x_5752_, v___x_5811_);
                        if v___x_5812_ == 0 {
                            leanh::lean_dec(v_snd_5808_);
                            leanh::lean_dec_ref(v_typeExpr_5726_);
                            v___y_5784_ = v_fst_5807_;
                            v___y_5785_ = v___x_5810_;
                            state = 6;
                            continue;
                        } else {
                            v___x_5813_ = lean_usize_of_nat(v___x_5811_);
                            v___x_5814_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2(v_typeExpr_5726_, v_snd_5808_, v___x_5813_, v___x_5799_, v___x_5810_);
                            leanh::lean_dec(v_snd_5808_);
                            v___y_5784_ = v_fst_5807_;
                            v___y_5785_ = v___x_5814_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_5755_, 1);
                        leanh::lean_dec(v_stx_5728_);
                        leanh::lean_dec_ref(v_typeExpr_5726_);
                        v_a_5815_ = leanh::lean_ctor_get(v___x_5804_, 0);
                        v_isSharedCheck_5822_ =
                            (!leanh::lean_is_exclusive(v___x_5804_)) as u8;
                        if v_isSharedCheck_5822_ == 0 {
                            v___x_5817_ = v___x_5804_;
                            v_isShared_5818_ = v_isSharedCheck_5822_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5815_);
                            leanh::lean_dec(v___x_5804_);
                            v___x_5817_ = leanh::lean_box(0);
                            v_isShared_5818_ = v_isSharedCheck_5822_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_5818_ == 0 {
                    v___x_5820_ = v___x_5817_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_a_5815_);
                    v___x_5820_ = v_reuseFailAlloc_5821_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___boxed(
    mut v_typeExpr_5840_: *mut leanh::LeanObject,
    mut v_ev_5841_: *mut leanh::LeanObject,
    mut v_stx_5842_: *mut leanh::LeanObject,
    mut v_a_5843_: *mut leanh::LeanObject,
    mut v_a_5844_: *mut leanh::LeanObject,
    mut v_a_5845_: *mut leanh::LeanObject,
    mut v_a_5846_: *mut leanh::LeanObject,
    mut v_a_5847_: *mut leanh::LeanObject,
    mut v_a_5848_: *mut leanh::LeanObject,
    mut v_a_5849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5850_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(
        v_typeExpr_5840_,
        v_ev_5841_,
        v_stx_5842_,
        v_a_5843_,
        v_a_5844_,
        v_a_5845_,
        v_a_5846_,
        v_a_5847_,
        v_a_5848_,
    );
    leanh::lean_dec(v_a_5848_);
    leanh::lean_dec_ref(v_a_5847_);
    leanh::lean_dec(v_a_5846_);
    leanh::lean_dec_ref(v_a_5845_);
    leanh::lean_dec(v_a_5844_);
    leanh::lean_dec_ref(v_a_5843_);
    return v_res_5850_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(
    mut v_00_u03b1_5851_: *mut leanh::LeanObject,
    mut v_typeExpr_5852_: *mut leanh::LeanObject,
    mut v_ev_5853_: *mut leanh::LeanObject,
    mut v_stx_5854_: *mut leanh::LeanObject,
    mut v_a_5855_: *mut leanh::LeanObject,
    mut v_a_5856_: *mut leanh::LeanObject,
    mut v_a_5857_: *mut leanh::LeanObject,
    mut v_a_5858_: *mut leanh::LeanObject,
    mut v_a_5859_: *mut leanh::LeanObject,
    mut v_a_5860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5862_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg(
        v_typeExpr_5852_,
        v_ev_5853_,
        v_stx_5854_,
        v_a_5855_,
        v_a_5856_,
        v_a_5857_,
        v_a_5858_,
        v_a_5859_,
        v_a_5860_,
    );
    return v___x_5862_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed(
    mut v_00_u03b1_5863_: *mut leanh::LeanObject,
    mut v_typeExpr_5864_: *mut leanh::LeanObject,
    mut v_ev_5865_: *mut leanh::LeanObject,
    mut v_stx_5866_: *mut leanh::LeanObject,
    mut v_a_5867_: *mut leanh::LeanObject,
    mut v_a_5868_: *mut leanh::LeanObject,
    mut v_a_5869_: *mut leanh::LeanObject,
    mut v_a_5870_: *mut leanh::LeanObject,
    mut v_a_5871_: *mut leanh::LeanObject,
    mut v_a_5872_: *mut leanh::LeanObject,
    mut v_a_5873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5874_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx(
        v_00_u03b1_5863_,
        v_typeExpr_5864_,
        v_ev_5865_,
        v_stx_5866_,
        v_a_5867_,
        v_a_5868_,
        v_a_5869_,
        v_a_5870_,
        v_a_5871_,
        v_a_5872_,
    );
    leanh::lean_dec(v_a_5872_);
    leanh::lean_dec_ref(v_a_5871_);
    leanh::lean_dec(v_a_5870_);
    leanh::lean_dec_ref(v_a_5869_);
    leanh::lean_dec(v_a_5868_);
    leanh::lean_dec_ref(v_a_5867_);
    return v_res_5874_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(
    mut v_00_u03b1_5875_: *mut leanh::LeanObject,
    mut v_ev_5876_: *mut leanh::LeanObject,
    mut v_sz_5877_: usize,
    mut v_i_5878_: usize,
    mut v_bs_5879_: *mut leanh::LeanObject,
    mut v___y_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
    mut v___y_5885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_5876_, v_sz_5877_, v_i_5878_, v_bs_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_);
    return v___x_5887_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___boxed(
    mut v_00_u03b1_5888_: *mut leanh::LeanObject,
    mut v_ev_5889_: *mut leanh::LeanObject,
    mut v_sz_5890_: *mut leanh::LeanObject,
    mut v_i_5891_: *mut leanh::LeanObject,
    mut v_bs_5892_: *mut leanh::LeanObject,
    mut v___y_5893_: *mut leanh::LeanObject,
    mut v___y_5894_: *mut leanh::LeanObject,
    mut v___y_5895_: *mut leanh::LeanObject,
    mut v___y_5896_: *mut leanh::LeanObject,
    mut v___y_5897_: *mut leanh::LeanObject,
    mut v___y_5898_: *mut leanh::LeanObject,
    mut v___y_5899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5900_: usize = 0;
    let mut v_i_boxed_5901_: usize = 0;
    let mut v_res_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5900_ = leanh::lean_unbox_usize(v_sz_5890_);
    leanh::lean_dec(v_sz_5890_);
    v_i_boxed_5901_ = leanh::lean_unbox_usize(v_i_5891_);
    leanh::lean_dec(v_i_5891_);
    v_res_5902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1(v_00_u03b1_5888_, v_ev_5889_, v_sz_boxed_5900_, v_i_boxed_5901_, v_bs_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
    leanh::lean_dec(v___y_5898_);
    leanh::lean_dec_ref(v___y_5897_);
    leanh::lean_dec(v___y_5896_);
    leanh::lean_dec_ref(v___y_5895_);
    leanh::lean_dec(v___y_5894_);
    leanh::lean_dec_ref(v___y_5893_);
    return v_res_5902_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(
    mut v_typeExpr_5903_: *mut leanh::LeanObject,
    mut v_as_5904_: *mut leanh::LeanObject,
    mut v_i_5905_: usize,
    mut v_stop_5906_: usize,
    mut v_b_5907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5908_: u8 = 0;
    let mut v___x_5909_: usize = 0;
    let mut v___x_5910_: usize = 0;
    let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5908_ = lean_usize_dec_eq(v_i_5905_, v_stop_5906_);
                if v___x_5908_ == 0 {
                    v___x_5909_ = 1usize;
                    v___x_5910_ = lean_usize_sub(v_i_5905_, v___x_5909_);
                    v___x_5911_ = lean_array_uget_borrowed(v_as_5904_, v___x_5910_);
                    v___x_5912_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__3);
                    leanh::lean_inc(v___x_5911_);
                    leanh::lean_inc_ref(v_typeExpr_5903_);
                    v___x_5913_ =
                        l_Lean_mkApp3(v___x_5912_, v_typeExpr_5903_, v___x_5911_, v_b_5907_);
                    v_i_5905_ = v___x_5910_;
                    v_b_5907_ = v___x_5913_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_typeExpr_5903_);
                    return v_b_5907_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0___boxed(
    mut v_typeExpr_5915_: *mut leanh::LeanObject,
    mut v_as_5916_: *mut leanh::LeanObject,
    mut v_i_5917_: *mut leanh::LeanObject,
    mut v_stop_5918_: *mut leanh::LeanObject,
    mut v_b_5919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5920_: usize = 0;
    let mut v_stop_boxed_5921_: usize = 0;
    let mut v_res_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5920_ = leanh::lean_unbox_usize(v_i_5917_);
    leanh::lean_dec(v_i_5917_);
    v_stop_boxed_5921_ = leanh::lean_unbox_usize(v_stop_5918_);
    leanh::lean_dec(v_stop_5918_);
    v_res_5922_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_5915_, v_as_5916_, v_i_boxed_5920_, v_stop_boxed_5921_, v_b_5919_);
    leanh::lean_dec_ref(v_as_5916_);
    return v_res_5922_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5926_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_5927_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1;
    v___x_5928_ = l_Lean_Expr_const___override(v___x_5927_, v___x_5926_);
    return v___x_5928_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(
    mut v_typeExpr_5933_: *mut leanh::LeanObject,
    mut v_ev_5934_: *mut leanh::LeanObject,
    mut v_stx_5935_: *mut leanh::LeanObject,
    mut v_a_5936_: *mut leanh::LeanObject,
    mut v_a_5937_: *mut leanh::LeanObject,
    mut v_a_5938_: *mut leanh::LeanObject,
    mut v_a_5939_: *mut leanh::LeanObject,
    mut v_a_5940_: *mut leanh::LeanObject,
    mut v_a_5941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5955_: u8 = 0;
    let mut v_cancelTk_x3f_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5957_: u8 = 0;
    let mut v_inheritedTraceOptions_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5969_: u8 = 0;
    let mut v___x_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: u8 = 0;
    let mut v___x_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v_unused_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5986_: u8 = 0;
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5990_: u8 = 0;
    let mut v___y_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: u8 = 0;
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6010_: usize = 0;
    let mut v___x_6011_: usize = 0;
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6015_: usize = 0;
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: u8 = 0;
    let mut v___x_6026_: usize = 0;
    let mut v___x_6027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6031_: u8 = 0;
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6035_: u8 = 0;
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: u8 = 0;
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: u8 = 0;
    let mut v___x_6045_: usize = 0;
    let mut v___x_6046_: usize = 0;
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: usize = 0;
    let mut v___x_6050_: usize = 0;
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_5943_ = leanh::lean_ctor_get(v_a_5940_, 0);
                v_fileMap_5944_ = leanh::lean_ctor_get(v_a_5940_, 1);
                v_options_5945_ = leanh::lean_ctor_get(v_a_5940_, 2);
                v_currRecDepth_5946_ = leanh::lean_ctor_get(v_a_5940_, 3);
                v_maxRecDepth_5947_ = leanh::lean_ctor_get(v_a_5940_, 4);
                v_ref_5948_ = leanh::lean_ctor_get(v_a_5940_, 5);
                v_currNamespace_5949_ = leanh::lean_ctor_get(v_a_5940_, 6);
                v_openDecls_5950_ = leanh::lean_ctor_get(v_a_5940_, 7);
                v_initHeartbeats_5951_ = leanh::lean_ctor_get(v_a_5940_, 8);
                v_maxHeartbeats_5952_ = leanh::lean_ctor_get(v_a_5940_, 9);
                v_quotContext_5953_ = leanh::lean_ctor_get(v_a_5940_, 10);
                v_currMacroScope_5954_ = leanh::lean_ctor_get(v_a_5940_, 11);
                v_diag_5955_ = leanh::lean_ctor_get_uint8(
                    v_a_5940_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_5956_ = leanh::lean_ctor_get(v_a_5940_, 12);
                v_suppressElabErrors_5957_ = leanh::lean_ctor_get_uint8(
                    v_a_5940_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5958_ = leanh::lean_ctor_get(v_a_5940_, 13);
                v___x_5959_ = leanh::lean_unsigned_to_nat(0);
                v___x_5960_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
                );
                v___x_5961_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2,
                );
                leanh::lean_inc_ref(v_typeExpr_5933_);
                v___x_5962_ = l_Lean_Expr_app___override(v___x_5961_, v_typeExpr_5933_);
                v___x_5963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5963_, 0, v___x_5962_);
                leanh::lean_inc(v_stx_5935_);
                v___x_6002_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_5935_,
                    );
                v___x_6003_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__5;
                leanh::lean_inc(v___x_6002_);
                v___x_6004_ = l_Lean_Syntax_isOfKind(v___x_6002_, v___x_6003_);
                if v___x_6004_ == 0 {
                    leanh::lean_dec(v___x_6002_);
                    leanh::lean_dec_ref_known(v___x_5963_, 1);
                    leanh::lean_dec(v_stx_5935_);
                    leanh::lean_dec_ref(v_ev_5934_);
                    leanh::lean_dec_ref(v_typeExpr_5933_);
                    v___x_6005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                    v___y_6001_ = v___x_6005_;
                    state = 7;
                    continue;
                } else {
                    v_ref_6006_ = l_Lean_replaceRef(v_stx_5935_, v_ref_5948_);
                    leanh::lean_inc_ref(v_inheritedTraceOptions_5958_);
                    leanh::lean_inc(v_cancelTk_x3f_5956_);
                    leanh::lean_inc(v_currMacroScope_5954_);
                    leanh::lean_inc(v_quotContext_5953_);
                    leanh::lean_inc(v_maxHeartbeats_5952_);
                    leanh::lean_inc(v_initHeartbeats_5951_);
                    leanh::lean_inc(v_openDecls_5950_);
                    leanh::lean_inc(v_currNamespace_5949_);
                    leanh::lean_inc(v_maxRecDepth_5947_);
                    leanh::lean_inc(v_currRecDepth_5946_);
                    leanh::lean_inc_ref(v_options_5945_);
                    leanh::lean_inc_ref(v_fileMap_5944_);
                    leanh::lean_inc_ref(v_fileName_5943_);
                    v___x_6007_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v___x_6007_, 0, v_fileName_5943_);
                    leanh::lean_ctor_set(v___x_6007_, 1, v_fileMap_5944_);
                    leanh::lean_ctor_set(v___x_6007_, 2, v_options_5945_);
                    leanh::lean_ctor_set(v___x_6007_, 3, v_currRecDepth_5946_);
                    leanh::lean_ctor_set(v___x_6007_, 4, v_maxRecDepth_5947_);
                    leanh::lean_ctor_set(v___x_6007_, 5, v_ref_6006_);
                    leanh::lean_ctor_set(v___x_6007_, 6, v_currNamespace_5949_);
                    leanh::lean_ctor_set(v___x_6007_, 7, v_openDecls_5950_);
                    leanh::lean_ctor_set(v___x_6007_, 8, v_initHeartbeats_5951_);
                    leanh::lean_ctor_set(v___x_6007_, 9, v_maxHeartbeats_5952_);
                    leanh::lean_ctor_set(v___x_6007_, 10, v_quotContext_5953_);
                    leanh::lean_ctor_set(v___x_6007_, 11, v_currMacroScope_5954_);
                    leanh::lean_ctor_set(v___x_6007_, 12, v_cancelTk_x3f_5956_);
                    leanh::lean_ctor_set(v___x_6007_, 13, v_inheritedTraceOptions_5958_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6007_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_5955_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_6007_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_5957_,
                    );
                    v___x_6036_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6037_ = l_Lean_Syntax_getArg(v___x_6002_, v___x_6036_);
                    leanh::lean_dec(v___x_6002_);
                    v___x_6038_ = l_Lean_Syntax_getArgs(v___x_6037_);
                    leanh::lean_dec(v___x_6037_);
                    v___x_6039_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__7;
                    v___x_6040_ = lean_array_get_size(v___x_6038_);
                    v___x_6041_ = lean_nat_dec_lt(v___x_5959_, v___x_6040_);
                    if v___x_6041_ == 0 {
                        leanh::lean_dec_ref(v___x_6038_);
                        v___y_6009_ = v___x_6039_;
                        state = 8;
                        continue;
                    } else {
                        v___x_6042_ = leanh::lean_box((v___x_6004_) as usize);
                        v___x_6043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6043_, 0, v___x_6042_);
                        leanh::lean_ctor_set(v___x_6043_, 1, v___x_6039_);
                        v___x_6044_ = lean_nat_dec_le(v___x_6040_, v___x_6040_);
                        if v___x_6044_ == 0 {
                            if v___x_6041_ == 0 {
                                leanh::lean_dec_ref_known(v___x_6043_, 2);
                                leanh::lean_dec_ref(v___x_6038_);
                                v___y_6009_ = v___x_6039_;
                                state = 8;
                                continue;
                            } else {
                                v___x_6045_ = 0usize;
                                v___x_6046_ = lean_usize_of_nat(v___x_6040_);
                                v___x_6047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_6004_, v___x_6038_, v___x_6045_, v___x_6046_, v___x_6043_);
                                leanh::lean_dec_ref(v___x_6038_);
                                v_snd_6048_ = leanh::lean_ctor_get(v___x_6047_, 1);
                                leanh::lean_inc(v_snd_6048_);
                                leanh::lean_dec_ref(v___x_6047_);
                                v___y_6009_ = v_snd_6048_;
                                state = 8;
                                continue;
                            }
                        } else {
                            v___x_6049_ = 0usize;
                            v___x_6050_ = lean_usize_of_nat(v___x_6040_);
                            v___x_6051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__3(v___x_6004_, v___x_6038_, v___x_6049_, v___x_6050_, v___x_6043_);
                            leanh::lean_dec_ref(v___x_6038_);
                            v_snd_6052_ = leanh::lean_ctor_get(v___x_6051_, 1);
                            leanh::lean_inc(v_snd_6052_);
                            leanh::lean_dec_ref(v___x_6051_);
                            v___y_6009_ = v_snd_6052_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5967_ = lean_st_ref_get(v_a_5941_);
                v_infoState_5968_ = leanh::lean_ctor_get(v___x_5967_, 7);
                leanh::lean_inc_ref(v_infoState_5968_);
                leanh::lean_dec(v___x_5967_);
                v_enabled_5969_ = leanh::lean_ctor_get_uint8(
                    v_infoState_5968_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_5968_);
                if v_enabled_5969_ == 0 {
                    leanh::lean_dec_ref(v_snd_5966_);
                    leanh::lean_dec_ref_known(v___x_5963_, 1);
                    leanh::lean_dec(v_stx_5935_);
                    v___x_5970_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5970_, 0, v_a_5965_);
                    return v___x_5970_;
                } else {
                    v___x_5971_ = leanh::lean_box(0);
                    v___x_5972_ = leanh::lean_box(0);
                    v___x_5973_ = 0;
                    v___x_5974_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_5935_,
                        v_snd_5966_,
                        v___x_5963_,
                        v___x_5971_,
                        v___x_5972_,
                        v___x_5973_,
                        v___x_5973_,
                        v_a_5936_,
                        v_a_5937_,
                        v_a_5938_,
                        v_a_5939_,
                        v_a_5940_,
                        v_a_5941_,
                    );
                    if leanh::lean_obj_tag(v___x_5974_) == 0 {
                        v_isSharedCheck_5981_ =
                            (!leanh::lean_is_exclusive(v___x_5974_)) as u8;
                        if v_isSharedCheck_5981_ == 0 {
                            v_unused_5982_ = leanh::lean_ctor_get(v___x_5974_, 0);
                            leanh::lean_dec(v_unused_5982_);
                            v___x_5976_ = v___x_5974_;
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_5974_);
                            v___x_5976_ = leanh::lean_box(0);
                            v_isShared_5977_ = v_isSharedCheck_5981_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_5965_);
                        v_a_5983_ = leanh::lean_ctor_get(v___x_5974_, 0);
                        v_isSharedCheck_5990_ =
                            (!leanh::lean_is_exclusive(v___x_5974_)) as u8;
                        if v_isSharedCheck_5990_ == 0 {
                            v___x_5985_ = v___x_5974_;
                            v_isShared_5986_ = v_isSharedCheck_5990_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5983_);
                            leanh::lean_dec(v___x_5974_);
                            v___x_5985_ = leanh::lean_box(0);
                            v_isShared_5986_ = v_isSharedCheck_5990_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5977_ == 0 {
                    leanh::lean_ctor_set(v___x_5976_, 0, v_a_5965_);
                    v___x_5979_ = v___x_5976_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5980_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5965_);
                    v___x_5979_ = v_reuseFailAlloc_5980_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5979_;
            }
            4 => {
                if v_isShared_5986_ == 0 {
                    v___x_5988_ = v___x_5985_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
                    v___x_5988_ = v_reuseFailAlloc_5989_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5988_;
            }
            6 => {
                v___x_5995_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__3;
                leanh::lean_inc_ref(v___y_5992_);
                v___x_5996_ = l_Lean_Name_mkStr2(v___y_5992_, v___x_5995_);
                v___x_5997_ = l_Lean_Expr_const___override(v___x_5996_, v___x_5960_);
                v___x_5998_ = l_Lean_mkAppB(v___x_5997_, v_typeExpr_5933_, v___y_5994_);
                leanh::lean_inc_ref(v___x_5998_);
                v___x_5999_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5999_, 0, v___y_5993_);
                leanh::lean_ctor_set(v___x_5999_, 1, v___x_5998_);
                v_a_5965_ = v___x_5999_;
                v_snd_5966_ = v___x_5998_;
                state = 1;
                continue;
            }
            7 => {
                return v___y_6001_;
            }
            8 => {
                v_sz_6010_ = lean_array_size(v___y_6009_);
                v___x_6011_ = 0usize;
                v___x_6012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__0(v_sz_6010_, v___x_6011_, v___y_6009_);
                if leanh::lean_obj_tag(v___x_6012_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6007_, 14);
                    leanh::lean_dec_ref_known(v___x_5963_, 1);
                    leanh::lean_dec(v_stx_5935_);
                    leanh::lean_dec_ref(v_ev_5934_);
                    leanh::lean_dec_ref(v_typeExpr_5933_);
                    v___x_6013_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                    v___y_6001_ = v___x_6013_;
                    state = 7;
                    continue;
                } else {
                    v_val_6014_ = leanh::lean_ctor_get(v___x_6012_, 0);
                    leanh::lean_inc(v_val_6014_);
                    leanh::lean_dec_ref_known(v___x_6012_, 1);
                    v_sz_6015_ = lean_array_size(v_val_6014_);
                    v___x_6016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__1___redArg(v_ev_5934_, v_sz_6015_, v___x_6011_, v_val_6014_, v_a_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v___x_6007_, v_a_5941_);
                    leanh::lean_dec_ref_known(v___x_6007_, 14);
                    if leanh::lean_obj_tag(v___x_6016_) == 0 {
                        v_a_6017_ = leanh::lean_ctor_get(v___x_6016_, 0);
                        leanh::lean_inc(v_a_6017_);
                        leanh::lean_dec_ref_known(v___x_6016_, 1);
                        v___x_6018_ = l_Array_unzip___redArg(v_a_6017_);
                        leanh::lean_dec(v_a_6017_);
                        v_fst_6019_ = leanh::lean_ctor_get(v___x_6018_, 0);
                        leanh::lean_inc(v_fst_6019_);
                        v_snd_6020_ = leanh::lean_ctor_get(v___x_6018_, 1);
                        leanh::lean_inc(v_snd_6020_);
                        leanh::lean_dec_ref(v___x_6018_);
                        v___x_6021_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__0;
                        v___x_6022_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6_once), _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__6);
                        leanh::lean_inc_ref(v_typeExpr_5933_);
                        v___x_6023_ = l_Lean_Expr_app___override(v___x_6022_, v_typeExpr_5933_);
                        v___x_6024_ = lean_array_get_size(v_snd_6020_);
                        v___x_6025_ = lean_nat_dec_lt(v___x_5959_, v___x_6024_);
                        if v___x_6025_ == 0 {
                            leanh::lean_dec(v_snd_6020_);
                            v___y_5992_ = v___x_6021_;
                            v___y_5993_ = v_fst_6019_;
                            v___y_5994_ = v___x_6023_;
                            state = 6;
                            continue;
                        } else {
                            v___x_6026_ = lean_usize_of_nat(v___x_6024_);
                            leanh::lean_inc_ref(v_typeExpr_5933_);
                            v___x_6027_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalArrayStx_spec__0(v_typeExpr_5933_, v_snd_6020_, v___x_6026_, v___x_6011_, v___x_6023_);
                            leanh::lean_dec(v_snd_6020_);
                            v___y_5992_ = v___x_6021_;
                            v___y_5993_ = v_fst_6019_;
                            v___y_5994_ = v___x_6027_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_5963_, 1);
                        leanh::lean_dec(v_stx_5935_);
                        leanh::lean_dec_ref(v_typeExpr_5933_);
                        v_a_6028_ = leanh::lean_ctor_get(v___x_6016_, 0);
                        v_isSharedCheck_6035_ =
                            (!leanh::lean_is_exclusive(v___x_6016_)) as u8;
                        if v_isSharedCheck_6035_ == 0 {
                            v___x_6030_ = v___x_6016_;
                            v_isShared_6031_ = v_isSharedCheck_6035_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6028_);
                            leanh::lean_dec(v___x_6016_);
                            v___x_6030_ = leanh::lean_box(0);
                            v_isShared_6031_ = v_isSharedCheck_6035_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_6031_ == 0 {
                    v___x_6033_ = v___x_6030_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6034_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_a_6028_);
                    v___x_6033_ = v_reuseFailAlloc_6034_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___boxed(
    mut v_typeExpr_6053_: *mut leanh::LeanObject,
    mut v_ev_6054_: *mut leanh::LeanObject,
    mut v_stx_6055_: *mut leanh::LeanObject,
    mut v_a_6056_: *mut leanh::LeanObject,
    mut v_a_6057_: *mut leanh::LeanObject,
    mut v_a_6058_: *mut leanh::LeanObject,
    mut v_a_6059_: *mut leanh::LeanObject,
    mut v_a_6060_: *mut leanh::LeanObject,
    mut v_a_6061_: *mut leanh::LeanObject,
    mut v_a_6062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6063_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(
        v_typeExpr_6053_,
        v_ev_6054_,
        v_stx_6055_,
        v_a_6056_,
        v_a_6057_,
        v_a_6058_,
        v_a_6059_,
        v_a_6060_,
        v_a_6061_,
    );
    leanh::lean_dec(v_a_6061_);
    leanh::lean_dec_ref(v_a_6060_);
    leanh::lean_dec(v_a_6059_);
    leanh::lean_dec_ref(v_a_6058_);
    leanh::lean_dec(v_a_6057_);
    leanh::lean_dec_ref(v_a_6056_);
    return v_res_6063_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(
    mut v_00_u03b1_6064_: *mut leanh::LeanObject,
    mut v_typeExpr_6065_: *mut leanh::LeanObject,
    mut v_ev_6066_: *mut leanh::LeanObject,
    mut v_stx_6067_: *mut leanh::LeanObject,
    mut v_a_6068_: *mut leanh::LeanObject,
    mut v_a_6069_: *mut leanh::LeanObject,
    mut v_a_6070_: *mut leanh::LeanObject,
    mut v_a_6071_: *mut leanh::LeanObject,
    mut v_a_6072_: *mut leanh::LeanObject,
    mut v_a_6073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6075_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg(
        v_typeExpr_6065_,
        v_ev_6066_,
        v_stx_6067_,
        v_a_6068_,
        v_a_6069_,
        v_a_6070_,
        v_a_6071_,
        v_a_6072_,
        v_a_6073_,
    );
    return v___x_6075_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed(
    mut v_00_u03b1_6076_: *mut leanh::LeanObject,
    mut v_typeExpr_6077_: *mut leanh::LeanObject,
    mut v_ev_6078_: *mut leanh::LeanObject,
    mut v_stx_6079_: *mut leanh::LeanObject,
    mut v_a_6080_: *mut leanh::LeanObject,
    mut v_a_6081_: *mut leanh::LeanObject,
    mut v_a_6082_: *mut leanh::LeanObject,
    mut v_a_6083_: *mut leanh::LeanObject,
    mut v_a_6084_: *mut leanh::LeanObject,
    mut v_a_6085_: *mut leanh::LeanObject,
    mut v_a_6086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6087_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx(
        v_00_u03b1_6076_,
        v_typeExpr_6077_,
        v_ev_6078_,
        v_stx_6079_,
        v_a_6080_,
        v_a_6081_,
        v_a_6082_,
        v_a_6083_,
        v_a_6084_,
        v_a_6085_,
    );
    leanh::lean_dec(v_a_6085_);
    leanh::lean_dec_ref(v_a_6084_);
    leanh::lean_dec(v_a_6083_);
    leanh::lean_dec_ref(v_a_6082_);
    leanh::lean_dec(v_a_6081_);
    leanh::lean_dec_ref(v_a_6080_);
    return v_res_6087_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6091_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__9,
    );
    v___x_6092_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__8,
    );
    v___x_6093_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6093_, 0, v___x_6092_);
    leanh::lean_ctor_set(v___x_6093_, 1, v___x_6091_);
    return v___x_6093_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6094_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2,
    );
    v___x_6095_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__1;
    v___x_6096_ = l_Lean_Expr_const___override(v___x_6095_, v___x_6094_);
    return v___x_6096_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6116_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__2,
    );
    v___x_6117_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__11;
    v___x_6118_ = l_Lean_Expr_const___override(v___x_6117_, v___x_6116_);
    return v___x_6118_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(
    mut v_typeExpr_6119_: *mut leanh::LeanObject,
    mut v_typeExpr_x27_6120_: *mut leanh::LeanObject,
    mut v_ev_6121_: *mut leanh::LeanObject,
    mut v_ev_x27_6122_: *mut leanh::LeanObject,
    mut v_stx_6123_: *mut leanh::LeanObject,
    mut v_a_6124_: *mut leanh::LeanObject,
    mut v_a_6125_: *mut leanh::LeanObject,
    mut v_a_6126_: *mut leanh::LeanObject,
    mut v_a_6127_: *mut leanh::LeanObject,
    mut v_a_6128_: *mut leanh::LeanObject,
    mut v_a_6129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6143_: u8 = 0;
    let mut v_cancelTk_x3f_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6145_: u8 = 0;
    let mut v_inheritedTraceOptions_6146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6156_: u8 = 0;
    let mut v___x_6157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: u8 = 0;
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6164_: u8 = 0;
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6168_: u8 = 0;
    let mut v_unused_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6173_: u8 = 0;
    let mut v___x_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6177_: u8 = 0;
    let mut v___y_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: u8 = 0;
    let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: u8 = 0;
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: u8 = 0;
    let mut v___x_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: u8 = 0;
    let mut v___x_6196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: u8 = 0;
    let mut v___x_6200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: u8 = 0;
    let mut v___x_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6214_: u8 = 0;
    let mut v_x_x27_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6222_: u8 = 0;
    let mut v___x_6224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_a_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut v_isSharedCheck_6240_: u8 = 0;
    let mut v_a_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6244_: u8 = 0;
    let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6131_ = leanh::lean_ctor_get(v_a_6128_, 0);
                v_fileMap_6132_ = leanh::lean_ctor_get(v_a_6128_, 1);
                v_options_6133_ = leanh::lean_ctor_get(v_a_6128_, 2);
                v_currRecDepth_6134_ = leanh::lean_ctor_get(v_a_6128_, 3);
                v_maxRecDepth_6135_ = leanh::lean_ctor_get(v_a_6128_, 4);
                v_ref_6136_ = leanh::lean_ctor_get(v_a_6128_, 5);
                v_currNamespace_6137_ = leanh::lean_ctor_get(v_a_6128_, 6);
                v_openDecls_6138_ = leanh::lean_ctor_get(v_a_6128_, 7);
                v_initHeartbeats_6139_ = leanh::lean_ctor_get(v_a_6128_, 8);
                v_maxHeartbeats_6140_ = leanh::lean_ctor_get(v_a_6128_, 9);
                v_quotContext_6141_ = leanh::lean_ctor_get(v_a_6128_, 10);
                v_currMacroScope_6142_ = leanh::lean_ctor_get(v_a_6128_, 11);
                v_diag_6143_ = leanh::lean_ctor_get_uint8(
                    v_a_6128_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6144_ = leanh::lean_ctor_get(v_a_6128_, 12);
                v_suppressElabErrors_6145_ = leanh::lean_ctor_get_uint8(
                    v_a_6128_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6146_ = leanh::lean_ctor_get(v_a_6128_, 13);
                v___x_6147_ = leanh::lean_unsigned_to_nat(0);
                v___x_6148_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3,
                );
                leanh::lean_inc_ref(v_typeExpr_x27_6120_);
                leanh::lean_inc_ref(v_typeExpr_6119_);
                v___x_6149_ = l_Lean_mkAppB(v___x_6148_, v_typeExpr_6119_, v_typeExpr_x27_6120_);
                v___x_6150_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6150_, 0, v___x_6149_);
                leanh::lean_inc(v_stx_6123_);
                v___x_6180_ =
                    l___private_Lean_Elab_ConfigEval_Basic_0__Lean_Elab_ConfigEval_stripParens(
                        v_stx_6123_,
                    );
                v___x_6181_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__5;
                leanh::lean_inc(v___x_6180_);
                v___x_6182_ = l_Lean_Syntax_isOfKind(v___x_6180_, v___x_6181_);
                if v___x_6182_ == 0 {
                    leanh::lean_dec(v___x_6180_);
                    leanh::lean_dec_ref_known(v___x_6150_, 1);
                    leanh::lean_dec(v_stx_6123_);
                    leanh::lean_dec_ref(v_ev_x27_6122_);
                    leanh::lean_dec_ref(v_ev_6121_);
                    leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                    leanh::lean_dec_ref(v_typeExpr_6119_);
                    v___x_6183_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                    v___y_6179_ = v___x_6183_;
                    state = 6;
                    continue;
                } else {
                    v___x_6184_ = l_Lean_Syntax_getArg(v___x_6180_, v___x_6147_);
                    v___x_6185_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__7;
                    leanh::lean_inc(v___x_6184_);
                    v___x_6186_ = l_Lean_Syntax_isOfKind(v___x_6184_, v___x_6185_);
                    if v___x_6186_ == 0 {
                        leanh::lean_dec(v___x_6184_);
                        leanh::lean_dec(v___x_6180_);
                        leanh::lean_dec_ref_known(v___x_6150_, 1);
                        leanh::lean_dec(v_stx_6123_);
                        leanh::lean_dec_ref(v_ev_x27_6122_);
                        leanh::lean_dec_ref(v_ev_6121_);
                        leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                        leanh::lean_dec_ref(v_typeExpr_6119_);
                        v___x_6187_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                        v___y_6179_ = v___x_6187_;
                        state = 6;
                        continue;
                    } else {
                        v___x_6188_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6189_ = l_Lean_Syntax_getArg(v___x_6184_, v___x_6188_);
                        leanh::lean_dec(v___x_6184_);
                        v___x_6190_ =
                            l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__9;
                        leanh::lean_inc(v___x_6189_);
                        v___x_6191_ = l_Lean_Syntax_isOfKind(v___x_6189_, v___x_6190_);
                        if v___x_6191_ == 0 {
                            leanh::lean_dec(v___x_6189_);
                            leanh::lean_dec(v___x_6180_);
                            leanh::lean_dec_ref_known(v___x_6150_, 1);
                            leanh::lean_dec(v_stx_6123_);
                            leanh::lean_dec_ref(v_ev_x27_6122_);
                            leanh::lean_dec_ref(v_ev_6121_);
                            leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                            leanh::lean_dec_ref(v_typeExpr_6119_);
                            v___x_6192_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                            v___y_6179_ = v___x_6192_;
                            state = 6;
                            continue;
                        } else {
                            v___x_6193_ = l_Lean_Syntax_getArg(v___x_6189_, v___x_6147_);
                            leanh::lean_dec(v___x_6189_);
                            v___x_6194_ = leanh::lean_box(0);
                            v___x_6195_ = l_Lean_Syntax_matchesIdent(v___x_6193_, v___x_6194_);
                            leanh::lean_dec(v___x_6193_);
                            if v___x_6195_ == 0 {
                                leanh::lean_dec(v___x_6180_);
                                leanh::lean_dec_ref_known(v___x_6150_, 1);
                                leanh::lean_dec(v_stx_6123_);
                                leanh::lean_dec_ref(v_ev_x27_6122_);
                                leanh::lean_dec_ref(v_ev_6121_);
                                leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                                leanh::lean_dec_ref(v_typeExpr_6119_);
                                v___x_6196_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                                v___y_6179_ = v___x_6196_;
                                state = 6;
                                continue;
                            } else {
                                v___x_6197_ = l_Lean_Syntax_getArg(v___x_6180_, v___x_6188_);
                                leanh::lean_dec(v___x_6180_);
                                v___x_6198_ = leanh::lean_unsigned_to_nat(3);
                                leanh::lean_inc(v___x_6197_);
                                v___x_6199_ = l_Lean_Syntax_matchesNull(v___x_6197_, v___x_6198_);
                                if v___x_6199_ == 0 {
                                    leanh::lean_dec(v___x_6197_);
                                    leanh::lean_dec_ref_known(v___x_6150_, 1);
                                    leanh::lean_dec(v_stx_6123_);
                                    leanh::lean_dec_ref(v_ev_x27_6122_);
                                    leanh::lean_dec_ref(v_ev_6121_);
                                    leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                                    leanh::lean_dec_ref(v_typeExpr_6119_);
                                    v___x_6200_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                                    v___y_6179_ = v___x_6200_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_6201_ = leanh::lean_unsigned_to_nat(2);
                                    v___x_6202_ = l_Lean_Syntax_getArg(v___x_6197_, v___x_6201_);
                                    leanh::lean_inc(v___x_6202_);
                                    v___x_6203_ =
                                        l_Lean_Syntax_matchesNull(v___x_6202_, v___x_6188_);
                                    if v___x_6203_ == 0 {
                                        leanh::lean_dec(v___x_6202_);
                                        leanh::lean_dec(v___x_6197_);
                                        leanh::lean_dec_ref_known(v___x_6150_, 1);
                                        leanh::lean_dec(v_stx_6123_);
                                        leanh::lean_dec_ref(v_ev_x27_6122_);
                                        leanh::lean_dec_ref(v_ev_6121_);
                                        leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                                        leanh::lean_dec_ref(v_typeExpr_6119_);
                                        v___x_6204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                                        v___y_6179_ = v___x_6204_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v_ref_6205_ = l_Lean_replaceRef(v_stx_6123_, v_ref_6136_);
                                        leanh::lean_inc_ref(v_inheritedTraceOptions_6146_);
                                        leanh::lean_inc(v_cancelTk_x3f_6144_);
                                        leanh::lean_inc(v_currMacroScope_6142_);
                                        leanh::lean_inc(v_quotContext_6141_);
                                        leanh::lean_inc(v_maxHeartbeats_6140_);
                                        leanh::lean_inc(v_initHeartbeats_6139_);
                                        leanh::lean_inc(v_openDecls_6138_);
                                        leanh::lean_inc(v_currNamespace_6137_);
                                        leanh::lean_inc(v_maxRecDepth_6135_);
                                        leanh::lean_inc(v_currRecDepth_6134_);
                                        leanh::lean_inc_ref(v_options_6133_);
                                        leanh::lean_inc_ref(v_fileMap_6132_);
                                        leanh::lean_inc_ref(v_fileName_6131_);
                                        v___x_6206_ =
                                            leanh::lean_alloc_ctor(0, 14, (2) as u32);
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            0,
                                            v_fileName_6131_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            1,
                                            v_fileMap_6132_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            2,
                                            v_options_6133_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            3,
                                            v_currRecDepth_6134_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            4,
                                            v_maxRecDepth_6135_,
                                        );
                                        leanh::lean_ctor_set(v___x_6206_, 5, v_ref_6205_);
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            6,
                                            v_currNamespace_6137_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            7,
                                            v_openDecls_6138_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            8,
                                            v_initHeartbeats_6139_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            9,
                                            v_maxHeartbeats_6140_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            10,
                                            v_quotContext_6141_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            11,
                                            v_currMacroScope_6142_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            12,
                                            v_cancelTk_x3f_6144_,
                                        );
                                        leanh::lean_ctor_set(
                                            v___x_6206_,
                                            13,
                                            v_inheritedTraceOptions_6146_,
                                        );
                                        leanh::lean_ctor_set_uint8(
                                            v___x_6206_,
                                            (core::mem::size_of::<*mut leanh::LeanObject>()
                                                * 14)
                                                as u32,
                                            v_diag_6143_,
                                        );
                                        leanh::lean_ctor_set_uint8(
                                            v___x_6206_,
                                            (core::mem::size_of::<*mut leanh::LeanObject>()
                                                * 14
                                                + 1)
                                                as u32,
                                            v_suppressElabErrors_6145_,
                                        );
                                        v_x_6207_ = l_Lean_Syntax_getArg(v___x_6197_, v___x_6147_);
                                        leanh::lean_dec(v___x_6197_);
                                        leanh::lean_inc(v_a_6129_);
                                        leanh::lean_inc_ref(v___x_6206_);
                                        leanh::lean_inc(v_a_6127_);
                                        leanh::lean_inc_ref(v_a_6126_);
                                        leanh::lean_inc(v_a_6125_);
                                        leanh::lean_inc_ref(v_a_6124_);
                                        v___x_6208_ = leanh::lean_apply_8(
                                            v_ev_6121_,
                                            v_x_6207_,
                                            v_a_6124_,
                                            v_a_6125_,
                                            v_a_6126_,
                                            v_a_6127_,
                                            v___x_6206_,
                                            v_a_6129_,
                                            leanh::lean_box(0),
                                        );
                                        if leanh::lean_obj_tag(v___x_6208_) == 0 {
                                            v_a_6209_ = leanh::lean_ctor_get(v___x_6208_, 0);
                                            leanh::lean_inc(v_a_6209_);
                                            leanh::lean_dec_ref_known(v___x_6208_, 1);
                                            v_fst_6210_ = leanh::lean_ctor_get(v_a_6209_, 0);
                                            v_snd_6211_ = leanh::lean_ctor_get(v_a_6209_, 1);
                                            v_isSharedCheck_6240_ =
                                                (!leanh::lean_is_exclusive(v_a_6209_)) as u8;
                                            if v_isSharedCheck_6240_ == 0 {
                                                v___x_6213_ = v_a_6209_;
                                                v_isShared_6214_ = v_isSharedCheck_6240_;
                                                state = 7;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_snd_6211_);
                                                leanh::lean_inc(v_fst_6210_);
                                                leanh::lean_dec(v_a_6209_);
                                                v___x_6213_ = leanh::lean_box(0);
                                                v_isShared_6214_ = v_isSharedCheck_6240_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v___x_6206_, 14);
                                            leanh::lean_dec(v___x_6202_);
                                            leanh::lean_dec_ref_known(v___x_6150_, 1);
                                            leanh::lean_dec(v_stx_6123_);
                                            leanh::lean_dec_ref(v_ev_x27_6122_);
                                            leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                                            leanh::lean_dec_ref(v_typeExpr_6119_);
                                            v_a_6241_ = leanh::lean_ctor_get(v___x_6208_, 0);
                                            v_isSharedCheck_6248_ =
                                                (!leanh::lean_is_exclusive(v___x_6208_))
                                                    as u8;
                                            if v_isSharedCheck_6248_ == 0 {
                                                v___x_6243_ = v___x_6208_;
                                                v_isShared_6244_ = v_isSharedCheck_6248_;
                                                state = 13;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_6241_);
                                                leanh::lean_dec(v___x_6208_);
                                                v___x_6243_ = leanh::lean_box(0);
                                                v_isShared_6244_ = v_isSharedCheck_6248_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6154_ = lean_st_ref_get(v_a_6129_);
                v_infoState_6155_ = leanh::lean_ctor_get(v___x_6154_, 7);
                leanh::lean_inc_ref(v_infoState_6155_);
                leanh::lean_dec(v___x_6154_);
                v_enabled_6156_ = leanh::lean_ctor_get_uint8(
                    v_infoState_6155_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_6155_);
                if v_enabled_6156_ == 0 {
                    leanh::lean_dec_ref(v_snd_6153_);
                    leanh::lean_dec_ref_known(v___x_6150_, 1);
                    leanh::lean_dec(v_stx_6123_);
                    v___x_6157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6157_, 0, v_a_6152_);
                    return v___x_6157_;
                } else {
                    v___x_6158_ = leanh::lean_box(0);
                    v___x_6159_ = leanh::lean_box(0);
                    v___x_6160_ = 0;
                    v___x_6161_ = l_Lean_Elab_Term_addTermInfo_x27(
                        v_stx_6123_,
                        v_snd_6153_,
                        v___x_6150_,
                        v___x_6158_,
                        v___x_6159_,
                        v___x_6160_,
                        v___x_6160_,
                        v_a_6124_,
                        v_a_6125_,
                        v_a_6126_,
                        v_a_6127_,
                        v_a_6128_,
                        v_a_6129_,
                    );
                    if leanh::lean_obj_tag(v___x_6161_) == 0 {
                        v_isSharedCheck_6168_ =
                            (!leanh::lean_is_exclusive(v___x_6161_)) as u8;
                        if v_isSharedCheck_6168_ == 0 {
                            v_unused_6169_ = leanh::lean_ctor_get(v___x_6161_, 0);
                            leanh::lean_dec(v_unused_6169_);
                            v___x_6163_ = v___x_6161_;
                            v_isShared_6164_ = v_isSharedCheck_6168_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6161_);
                            v___x_6163_ = leanh::lean_box(0);
                            v_isShared_6164_ = v_isSharedCheck_6168_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_6152_);
                        v_a_6170_ = leanh::lean_ctor_get(v___x_6161_, 0);
                        v_isSharedCheck_6177_ =
                            (!leanh::lean_is_exclusive(v___x_6161_)) as u8;
                        if v_isSharedCheck_6177_ == 0 {
                            v___x_6172_ = v___x_6161_;
                            v_isShared_6173_ = v_isSharedCheck_6177_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6170_);
                            leanh::lean_dec(v___x_6161_);
                            v___x_6172_ = leanh::lean_box(0);
                            v_isShared_6173_ = v_isSharedCheck_6177_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_6164_ == 0 {
                    leanh::lean_ctor_set(v___x_6163_, 0, v_a_6152_);
                    v___x_6166_ = v___x_6163_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6167_, 0, v_a_6152_);
                    v___x_6166_ = v_reuseFailAlloc_6167_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6166_;
            }
            4 => {
                if v_isShared_6173_ == 0 {
                    v___x_6175_ = v___x_6172_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6176_, 0, v_a_6170_);
                    v___x_6175_ = v_reuseFailAlloc_6176_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6175_;
            }
            6 => {
                return v___y_6179_;
            }
            7 => {
                v_x_x27_6215_ = l_Lean_Syntax_getArg(v___x_6202_, v___x_6147_);
                leanh::lean_dec(v___x_6202_);
                leanh::lean_inc(v_a_6129_);
                leanh::lean_inc(v_a_6127_);
                leanh::lean_inc_ref(v_a_6126_);
                leanh::lean_inc(v_a_6125_);
                leanh::lean_inc_ref(v_a_6124_);
                v___x_6216_ = leanh::lean_apply_8(
                    v_ev_x27_6122_,
                    v_x_x27_6215_,
                    v_a_6124_,
                    v_a_6125_,
                    v_a_6126_,
                    v_a_6127_,
                    v___x_6206_,
                    v_a_6129_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6216_) == 0 {
                    v_a_6217_ = leanh::lean_ctor_get(v___x_6216_, 0);
                    leanh::lean_inc(v_a_6217_);
                    leanh::lean_dec_ref_known(v___x_6216_, 1);
                    v_fst_6218_ = leanh::lean_ctor_get(v_a_6217_, 0);
                    v_snd_6219_ = leanh::lean_ctor_get(v_a_6217_, 1);
                    v_isSharedCheck_6231_ = (!leanh::lean_is_exclusive(v_a_6217_)) as u8;
                    if v_isSharedCheck_6231_ == 0 {
                        v___x_6221_ = v_a_6217_;
                        v_isShared_6222_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6219_);
                        leanh::lean_inc(v_fst_6218_);
                        leanh::lean_dec(v_a_6217_);
                        v___x_6221_ = leanh::lean_box(0);
                        v_isShared_6222_ = v_isSharedCheck_6231_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6213_);
                    leanh::lean_dec(v_snd_6211_);
                    leanh::lean_dec(v_fst_6210_);
                    leanh::lean_dec_ref_known(v___x_6150_, 1);
                    leanh::lean_dec(v_stx_6123_);
                    leanh::lean_dec_ref(v_typeExpr_x27_6120_);
                    leanh::lean_dec_ref(v_typeExpr_6119_);
                    v_a_6232_ = leanh::lean_ctor_get(v___x_6216_, 0);
                    v_isSharedCheck_6239_ = (!leanh::lean_is_exclusive(v___x_6216_)) as u8;
                    if v_isSharedCheck_6239_ == 0 {
                        v___x_6234_ = v___x_6216_;
                        v_isShared_6235_ = v_isSharedCheck_6239_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6232_);
                        leanh::lean_dec(v___x_6216_);
                        v___x_6234_ = leanh::lean_box(0);
                        v_isShared_6235_ = v_isSharedCheck_6239_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_6222_ == 0 {
                    leanh::lean_ctor_set(v___x_6221_, 1, v_fst_6218_);
                    leanh::lean_ctor_set(v___x_6221_, 0, v_fst_6210_);
                    v___x_6224_ = v___x_6221_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_fst_6210_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6230_, 1, v_fst_6218_);
                    v___x_6224_ = v_reuseFailAlloc_6230_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6225_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__12,
                );
                v___x_6226_ = l_Lean_mkApp4(
                    v___x_6225_,
                    v_typeExpr_6119_,
                    v_typeExpr_x27_6120_,
                    v_snd_6211_,
                    v_snd_6219_,
                );
                leanh::lean_inc_ref(v___x_6226_);
                if v_isShared_6214_ == 0 {
                    leanh::lean_ctor_set(v___x_6213_, 1, v___x_6226_);
                    leanh::lean_ctor_set(v___x_6213_, 0, v___x_6224_);
                    v___x_6228_ = v___x_6213_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6229_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6229_, 0, v___x_6224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6229_, 1, v___x_6226_);
                    v___x_6228_ = v_reuseFailAlloc_6229_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_6152_ = v___x_6228_;
                v_snd_6153_ = v___x_6226_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_6235_ == 0 {
                    v___x_6237_ = v___x_6234_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
                    v___x_6237_ = v_reuseFailAlloc_6238_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6237_;
            }
            13 => {
                if v_isShared_6244_ == 0 {
                    v___x_6246_ = v___x_6243_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6247_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6247_, 0, v_a_6241_);
                    v___x_6246_ = v_reuseFailAlloc_6247_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6246_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___boxed(
    mut v_typeExpr_6249_: *mut leanh::LeanObject,
    mut v_typeExpr_x27_6250_: *mut leanh::LeanObject,
    mut v_ev_6251_: *mut leanh::LeanObject,
    mut v_ev_x27_6252_: *mut leanh::LeanObject,
    mut v_stx_6253_: *mut leanh::LeanObject,
    mut v_a_6254_: *mut leanh::LeanObject,
    mut v_a_6255_: *mut leanh::LeanObject,
    mut v_a_6256_: *mut leanh::LeanObject,
    mut v_a_6257_: *mut leanh::LeanObject,
    mut v_a_6258_: *mut leanh::LeanObject,
    mut v_a_6259_: *mut leanh::LeanObject,
    mut v_a_6260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6261_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(
        v_typeExpr_6249_,
        v_typeExpr_x27_6250_,
        v_ev_6251_,
        v_ev_x27_6252_,
        v_stx_6253_,
        v_a_6254_,
        v_a_6255_,
        v_a_6256_,
        v_a_6257_,
        v_a_6258_,
        v_a_6259_,
    );
    leanh::lean_dec(v_a_6259_);
    leanh::lean_dec_ref(v_a_6258_);
    leanh::lean_dec(v_a_6257_);
    leanh::lean_dec_ref(v_a_6256_);
    leanh::lean_dec(v_a_6255_);
    leanh::lean_dec_ref(v_a_6254_);
    return v_res_6261_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(
    mut v_00_u03b1_6262_: *mut leanh::LeanObject,
    mut v_00_u03b1_x27_6263_: *mut leanh::LeanObject,
    mut v_typeExpr_6264_: *mut leanh::LeanObject,
    mut v_typeExpr_x27_6265_: *mut leanh::LeanObject,
    mut v_ev_6266_: *mut leanh::LeanObject,
    mut v_ev_x27_6267_: *mut leanh::LeanObject,
    mut v_stx_6268_: *mut leanh::LeanObject,
    mut v_a_6269_: *mut leanh::LeanObject,
    mut v_a_6270_: *mut leanh::LeanObject,
    mut v_a_6271_: *mut leanh::LeanObject,
    mut v_a_6272_: *mut leanh::LeanObject,
    mut v_a_6273_: *mut leanh::LeanObject,
    mut v_a_6274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6276_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg(
        v_typeExpr_6264_,
        v_typeExpr_x27_6265_,
        v_ev_6266_,
        v_ev_x27_6267_,
        v_stx_6268_,
        v_a_6269_,
        v_a_6270_,
        v_a_6271_,
        v_a_6272_,
        v_a_6273_,
        v_a_6274_,
    );
    return v___x_6276_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed(
    mut v_00_u03b1_6277_: *mut leanh::LeanObject,
    mut v_00_u03b1_x27_6278_: *mut leanh::LeanObject,
    mut v_typeExpr_6279_: *mut leanh::LeanObject,
    mut v_typeExpr_x27_6280_: *mut leanh::LeanObject,
    mut v_ev_6281_: *mut leanh::LeanObject,
    mut v_ev_x27_6282_: *mut leanh::LeanObject,
    mut v_stx_6283_: *mut leanh::LeanObject,
    mut v_a_6284_: *mut leanh::LeanObject,
    mut v_a_6285_: *mut leanh::LeanObject,
    mut v_a_6286_: *mut leanh::LeanObject,
    mut v_a_6287_: *mut leanh::LeanObject,
    mut v_a_6288_: *mut leanh::LeanObject,
    mut v_a_6289_: *mut leanh::LeanObject,
    mut v_a_6290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6291_ = l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx(
        v_00_u03b1_6277_,
        v_00_u03b1_x27_6278_,
        v_typeExpr_6279_,
        v_typeExpr_x27_6280_,
        v_ev_6281_,
        v_ev_x27_6282_,
        v_stx_6283_,
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
    leanh::lean_dec(v_a_6285_);
    leanh::lean_dec_ref(v_a_6284_);
    return v_res_6291_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(
    mut v_00_u03b1_6292_: *mut leanh::LeanObject,
    mut v_c_6293_: *mut leanh::LeanObject,
    mut v_f_6294_: *mut leanh::LeanObject,
    mut v_x_6295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6300_: u8 = 0;
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6296_ = leanh::lean_ctor_get(v_x_6295_, 0);
                v_snd_6297_ = leanh::lean_ctor_get(v_x_6295_, 1);
                v_isSharedCheck_6308_ = (!leanh::lean_is_exclusive(v_x_6295_)) as u8;
                if v_isSharedCheck_6308_ == 0 {
                    v___x_6299_ = v_x_6295_;
                    v_isShared_6300_ = v_isSharedCheck_6308_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6297_);
                    leanh::lean_inc(v_fst_6296_);
                    leanh::lean_dec(v_x_6295_);
                    v___x_6299_ = leanh::lean_box(0);
                    v_isShared_6300_ = v_isSharedCheck_6308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6301_ = leanh::lean_apply_1(v_f_6294_, v_fst_6296_);
                v___x_6302_ = leanh::lean_box(0);
                v___x_6303_ = l_Lean_Expr_const___override(v_c_6293_, v___x_6302_);
                v___x_6304_ = l_Lean_Expr_app___override(v___x_6303_, v_snd_6297_);
                if v_isShared_6300_ == 0 {
                    leanh::lean_ctor_set(v___x_6299_, 1, v___x_6304_);
                    leanh::lean_ctor_set(v___x_6299_, 0, v___x_6301_);
                    v___x_6306_ = v___x_6299_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6307_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6307_, 0, v___x_6301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6307_, 1, v___x_6304_);
                    v___x_6306_ = v_reuseFailAlloc_6307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(
    mut v_v_6309_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6310_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_6310_, 0 as u32, v_v_6309_);
    return v___x_6310_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1___boxed(
    mut v_v_6311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_6312_: u8 = 0;
    let mut v_res_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_6312_ = (leanh::lean_unbox(v_v_6311_) as u8);
    v_res_6313_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__1(v_v_boxed_6312_);
    return v_res_6313_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__2(
    mut v_v_6314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6315_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6315_, 0, v_v_6314_);
    return v___x_6315_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__3(
    mut v_v_6316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6317_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6317_, 0, v_v_6316_);
    return v___x_6317_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__4(
    mut v_v_6318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6319_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6319_, 0, v_v_6318_);
    return v___x_6319_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__5(
    mut v_v_6320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6321_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6321_, 0, v_v_6320_);
    return v___x_6321_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(
    mut v_stx_6353_: *mut leanh::LeanObject,
    mut v_a_6354_: *mut leanh::LeanObject,
    mut v_a_6355_: *mut leanh::LeanObject,
    mut v_a_6356_: *mut leanh::LeanObject,
    mut v_a_6357_: *mut leanh::LeanObject,
    mut v_a_6358_: *mut leanh::LeanObject,
    mut v_a_6359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6364_: u8 = 0;
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6370_: u8 = 0;
    let mut v___x_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6374_: u8 = 0;
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6381_: u8 = 0;
    let mut v___f_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6388_: u8 = 0;
    let mut v_a_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6392_: u8 = 0;
    let mut v___f_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6399_: u8 = 0;
    let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6407_: u8 = 0;
    let mut v___x_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6413_: u8 = 0;
    let mut v_a_6414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6417_: u8 = 0;
    let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: u8 = 0;
    let mut v___x_6421_: u8 = 0;
    let mut v_reuseFailAlloc_6422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6423_: u8 = 0;
    let mut v_a_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6427_: u8 = 0;
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6431_: u8 = 0;
    let mut v_a_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6435_: u8 = 0;
    let mut v___x_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6439_: u8 = 0;
    let mut v___y_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6443_: u8 = 0;
    let mut v___x_6444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6451_: u8 = 0;
    let mut v___x_6452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6457_: u8 = 0;
    let mut v_a_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6461_: u8 = 0;
    let mut v___x_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: u8 = 0;
    let mut v___x_6465_: u8 = 0;
    let mut v_reuseFailAlloc_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6467_: u8 = 0;
    let mut v_a_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6471_: u8 = 0;
    let mut v___x_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6475_: u8 = 0;
    let mut v_a_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6479_: u8 = 0;
    let mut v___x_6481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6483_: u8 = 0;
    let mut v___f_6484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6488_: u8 = 0;
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6496_: u8 = 0;
    let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6502_: u8 = 0;
    let mut v_a_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6506_: u8 = 0;
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: u8 = 0;
    let mut v___x_6510_: u8 = 0;
    let mut v_reuseFailAlloc_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6512_: u8 = 0;
    let mut v_a_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6516_: u8 = 0;
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6520_: u8 = 0;
    let mut v_a_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6524_: u8 = 0;
    let mut v___x_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v___x_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6532_: u8 = 0;
    let mut v___x_6533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6540_: u8 = 0;
    let mut v___x_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6546_: u8 = 0;
    let mut v_a_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6550_: u8 = 0;
    let mut v___x_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: u8 = 0;
    let mut v___x_6554_: u8 = 0;
    let mut v_reuseFailAlloc_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6556_: u8 = 0;
    let mut v_a_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6560_: u8 = 0;
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6564_: u8 = 0;
    let mut v_a_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6568_: u8 = 0;
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6572_: u8 = 0;
    let mut v___x_6573_: u8 = 0;
    let mut v___x_6574_: u8 = 0;
    let mut v_reuseFailAlloc_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6576_: u8 = 0;
    let mut v_a_6577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6580_: u8 = 0;
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6375_ = l_Lean_Meta_saveState___redArg(v_a_6357_, v_a_6359_);
                if leanh::lean_obj_tag(v___x_6375_) == 0 {
                    v_a_6376_ = leanh::lean_ctor_get(v___x_6375_, 0);
                    leanh::lean_inc(v_a_6376_);
                    leanh::lean_dec_ref_known(v___x_6375_, 1);
                    leanh::lean_inc(v_stx_6353_);
                    v___x_6377_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx(
                        v_stx_6353_,
                        v_a_6354_,
                        v_a_6355_,
                        v_a_6356_,
                        v_a_6357_,
                        v_a_6358_,
                        v_a_6359_,
                    );
                    if leanh::lean_obj_tag(v___x_6377_) == 0 {
                        leanh::lean_dec(v_a_6376_);
                        leanh::lean_dec(v_stx_6353_);
                        v_a_6378_ = leanh::lean_ctor_get(v___x_6377_, 0);
                        v_isSharedCheck_6388_ =
                            (!leanh::lean_is_exclusive(v___x_6377_)) as u8;
                        if v_isSharedCheck_6388_ == 0 {
                            v___x_6380_ = v___x_6377_;
                            v_isShared_6381_ = v_isSharedCheck_6388_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6378_);
                            leanh::lean_dec(v___x_6377_);
                            v___x_6380_ = leanh::lean_box(0);
                            v_isShared_6381_ = v_isSharedCheck_6388_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_6389_ = leanh::lean_ctor_get(v___x_6377_, 0);
                        v_isSharedCheck_6576_ =
                            (!leanh::lean_is_exclusive(v___x_6377_)) as u8;
                        if v_isSharedCheck_6576_ == 0 {
                            v___x_6391_ = v___x_6377_;
                            v_isShared_6392_ = v_isSharedCheck_6576_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6389_);
                            leanh::lean_dec(v___x_6377_);
                            v___x_6391_ = leanh::lean_box(0);
                            v_isShared_6392_ = v_isSharedCheck_6576_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_stx_6353_);
                    v_a_6577_ = leanh::lean_ctor_get(v___x_6375_, 0);
                    v_isSharedCheck_6584_ = (!leanh::lean_is_exclusive(v___x_6375_)) as u8;
                    if v_isSharedCheck_6584_ == 0 {
                        v___x_6579_ = v___x_6375_;
                        v_isShared_6580_ = v_isSharedCheck_6584_;
                        state = 44;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6577_);
                        leanh::lean_dec(v___x_6375_);
                        v___x_6579_ = leanh::lean_box(0);
                        v_isShared_6580_ = v_isSharedCheck_6584_;
                        state = 44;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6364_ == 0 {
                    leanh::lean_dec_ref(v___y_6362_);
                    v___x_6365_ =
                        l_Lean_Meta_SavedState_restore___redArg(v___y_6363_, v_a_6357_, v_a_6359_);
                    leanh::lean_dec_ref(v___y_6363_);
                    if leanh::lean_obj_tag(v___x_6365_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6365_, 1);
                        v___x_6366_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ConfigEval_EvalTerm_evalBoolStx_spec__0___redArg();
                        return v___x_6366_;
                    } else {
                        v_a_6367_ = leanh::lean_ctor_get(v___x_6365_, 0);
                        v_isSharedCheck_6374_ =
                            (!leanh::lean_is_exclusive(v___x_6365_)) as u8;
                        if v_isSharedCheck_6374_ == 0 {
                            v___x_6369_ = v___x_6365_;
                            v_isShared_6370_ = v_isSharedCheck_6374_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6367_);
                            leanh::lean_dec(v___x_6365_);
                            v___x_6369_ = leanh::lean_box(0);
                            v_isShared_6370_ = v_isSharedCheck_6374_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6363_);
                    return v___y_6362_;
                }
            }
            2 => {
                if v_isShared_6370_ == 0 {
                    v___x_6372_ = v___x_6369_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_a_6367_);
                    v___x_6372_ = v_reuseFailAlloc_6373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6372_;
            }
            4 => {
                v___f_6382_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__1;
                v___x_6383_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3;
                v___x_6384_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(
                    leanh::lean_box(0),
                    v___x_6383_,
                    v___f_6382_,
                    v_a_6378_,
                );
                if v_isShared_6381_ == 0 {
                    leanh::lean_ctor_set(v___x_6380_, 0, v___x_6384_);
                    v___x_6386_ = v___x_6380_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6387_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6387_, 0, v___x_6384_);
                    v___x_6386_ = v_reuseFailAlloc_6387_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6386_;
            }
            6 => {
                v___f_6393_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__4;
                v___f_6394_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__5;
                v___f_6395_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__6;
                v___f_6484_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__11;
                leanh::lean_inc(v_a_6389_);
                if v_isShared_6392_ == 0 {
                    v___x_6530_ = v___x_6391_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6575_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_a_6389_);
                    v___x_6530_ = v_reuseFailAlloc_6575_;
                    state = 34;
                    continue;
                }
            }
            7 => {
                if v___y_6399_ == 0 {
                    leanh::lean_dec_ref(v___y_6397_);
                    v___x_6400_ =
                        l_Lean_Meta_SavedState_restore___redArg(v___y_6398_, v_a_6357_, v_a_6359_);
                    leanh::lean_dec_ref(v___y_6398_);
                    if leanh::lean_obj_tag(v___x_6400_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6400_, 1);
                        v___x_6401_ = l_Lean_Meta_saveState___redArg(v_a_6357_, v_a_6359_);
                        if leanh::lean_obj_tag(v___x_6401_) == 0 {
                            v_a_6402_ = leanh::lean_ctor_get(v___x_6401_, 0);
                            leanh::lean_inc(v_a_6402_);
                            leanh::lean_dec_ref_known(v___x_6401_, 1);
                            v___x_6403_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx(
                                v_stx_6353_,
                                v_a_6354_,
                                v_a_6355_,
                                v_a_6356_,
                                v_a_6357_,
                                v_a_6358_,
                                v_a_6359_,
                            );
                            if leanh::lean_obj_tag(v___x_6403_) == 0 {
                                leanh::lean_dec(v_a_6402_);
                                v_a_6404_ = leanh::lean_ctor_get(v___x_6403_, 0);
                                v_isSharedCheck_6413_ =
                                    (!leanh::lean_is_exclusive(v___x_6403_)) as u8;
                                if v_isSharedCheck_6413_ == 0 {
                                    v___x_6406_ = v___x_6403_;
                                    v_isShared_6407_ = v_isSharedCheck_6413_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6404_);
                                    leanh::lean_dec(v___x_6403_);
                                    v___x_6406_ = leanh::lean_box(0);
                                    v_isShared_6407_ = v_isSharedCheck_6413_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v_a_6414_ = leanh::lean_ctor_get(v___x_6403_, 0);
                                v_isSharedCheck_6423_ =
                                    (!leanh::lean_is_exclusive(v___x_6403_)) as u8;
                                if v_isSharedCheck_6423_ == 0 {
                                    v___x_6416_ = v___x_6403_;
                                    v_isShared_6417_ = v_isSharedCheck_6423_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6414_);
                                    leanh::lean_dec(v___x_6403_);
                                    v___x_6416_ = leanh::lean_box(0);
                                    v_isShared_6417_ = v_isSharedCheck_6423_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_stx_6353_);
                            v_a_6424_ = leanh::lean_ctor_get(v___x_6401_, 0);
                            v_isSharedCheck_6431_ =
                                (!leanh::lean_is_exclusive(v___x_6401_)) as u8;
                            if v_isSharedCheck_6431_ == 0 {
                                v___x_6426_ = v___x_6401_;
                                v_isShared_6427_ = v_isSharedCheck_6431_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6424_);
                                leanh::lean_dec(v___x_6401_);
                                v___x_6426_ = leanh::lean_box(0);
                                v_isShared_6427_ = v_isSharedCheck_6431_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_stx_6353_);
                        v_a_6432_ = leanh::lean_ctor_get(v___x_6400_, 0);
                        v_isSharedCheck_6439_ =
                            (!leanh::lean_is_exclusive(v___x_6400_)) as u8;
                        if v_isSharedCheck_6439_ == 0 {
                            v___x_6434_ = v___x_6400_;
                            v_isShared_6435_ = v_isSharedCheck_6439_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6432_);
                            leanh::lean_dec(v___x_6400_);
                            v___x_6434_ = leanh::lean_box(0);
                            v_isShared_6435_ = v_isSharedCheck_6439_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6398_);
                    leanh::lean_dec(v_stx_6353_);
                    return v___y_6397_;
                }
            }
            8 => {
                v___x_6408_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8;
                v___x_6409_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(
                    leanh::lean_box(0),
                    v___x_6408_,
                    v___f_6395_,
                    v_a_6404_,
                );
                if v_isShared_6407_ == 0 {
                    leanh::lean_ctor_set(v___x_6406_, 0, v___x_6409_);
                    v___x_6411_ = v___x_6406_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6412_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6412_, 0, v___x_6409_);
                    v___x_6411_ = v_reuseFailAlloc_6412_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6411_;
            }
            10 => {
                leanh::lean_inc(v_a_6414_);
                if v_isShared_6417_ == 0 {
                    v___x_6419_ = v___x_6416_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6422_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6422_, 0, v_a_6414_);
                    v___x_6419_ = v_reuseFailAlloc_6422_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_6420_ = l_Lean_Exception_isInterrupt(v_a_6414_);
                if v___x_6420_ == 0 {
                    v___x_6421_ = l_Lean_Exception_isRuntime(v_a_6414_);
                    v___y_6362_ = v___x_6419_;
                    v___y_6363_ = v_a_6402_;
                    v___y_6364_ = v___x_6421_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6414_);
                    v___y_6362_ = v___x_6419_;
                    v___y_6363_ = v_a_6402_;
                    v___y_6364_ = v___x_6420_;
                    state = 1;
                    continue;
                }
            }
            12 => {
                if v_isShared_6427_ == 0 {
                    v___x_6429_ = v___x_6426_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6430_, 0, v_a_6424_);
                    v___x_6429_ = v_reuseFailAlloc_6430_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6429_;
            }
            14 => {
                if v_isShared_6435_ == 0 {
                    v___x_6437_ = v___x_6434_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6438_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6438_, 0, v_a_6432_);
                    v___x_6437_ = v_reuseFailAlloc_6438_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6437_;
            }
            16 => {
                if v___y_6443_ == 0 {
                    leanh::lean_dec_ref(v___y_6441_);
                    v___x_6444_ =
                        l_Lean_Meta_SavedState_restore___redArg(v___y_6442_, v_a_6357_, v_a_6359_);
                    leanh::lean_dec_ref(v___y_6442_);
                    if leanh::lean_obj_tag(v___x_6444_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6444_, 1);
                        v___x_6445_ = l_Lean_Meta_saveState___redArg(v_a_6357_, v_a_6359_);
                        if leanh::lean_obj_tag(v___x_6445_) == 0 {
                            v_a_6446_ = leanh::lean_ctor_get(v___x_6445_, 0);
                            leanh::lean_inc(v_a_6446_);
                            leanh::lean_dec_ref_known(v___x_6445_, 1);
                            leanh::lean_inc(v_stx_6353_);
                            v___x_6447_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx(
                                v_stx_6353_,
                                v_a_6354_,
                                v_a_6355_,
                                v_a_6356_,
                                v_a_6357_,
                                v_a_6358_,
                                v_a_6359_,
                            );
                            if leanh::lean_obj_tag(v___x_6447_) == 0 {
                                leanh::lean_dec(v_a_6446_);
                                leanh::lean_dec(v_stx_6353_);
                                v_a_6448_ = leanh::lean_ctor_get(v___x_6447_, 0);
                                v_isSharedCheck_6457_ =
                                    (!leanh::lean_is_exclusive(v___x_6447_)) as u8;
                                if v_isSharedCheck_6457_ == 0 {
                                    v___x_6450_ = v___x_6447_;
                                    v_isShared_6451_ = v_isSharedCheck_6457_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6448_);
                                    leanh::lean_dec(v___x_6447_);
                                    v___x_6450_ = leanh::lean_box(0);
                                    v_isShared_6451_ = v_isSharedCheck_6457_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                v_a_6458_ = leanh::lean_ctor_get(v___x_6447_, 0);
                                v_isSharedCheck_6467_ =
                                    (!leanh::lean_is_exclusive(v___x_6447_)) as u8;
                                if v_isSharedCheck_6467_ == 0 {
                                    v___x_6460_ = v___x_6447_;
                                    v_isShared_6461_ = v_isSharedCheck_6467_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6458_);
                                    leanh::lean_dec(v___x_6447_);
                                    v___x_6460_ = leanh::lean_box(0);
                                    v_isShared_6461_ = v_isSharedCheck_6467_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_stx_6353_);
                            v_a_6468_ = leanh::lean_ctor_get(v___x_6445_, 0);
                            v_isSharedCheck_6475_ =
                                (!leanh::lean_is_exclusive(v___x_6445_)) as u8;
                            if v_isSharedCheck_6475_ == 0 {
                                v___x_6470_ = v___x_6445_;
                                v_isShared_6471_ = v_isSharedCheck_6475_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6468_);
                                leanh::lean_dec(v___x_6445_);
                                v___x_6470_ = leanh::lean_box(0);
                                v_isShared_6471_ = v_isSharedCheck_6475_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_stx_6353_);
                        v_a_6476_ = leanh::lean_ctor_get(v___x_6444_, 0);
                        v_isSharedCheck_6483_ =
                            (!leanh::lean_is_exclusive(v___x_6444_)) as u8;
                        if v_isSharedCheck_6483_ == 0 {
                            v___x_6478_ = v___x_6444_;
                            v_isShared_6479_ = v_isSharedCheck_6483_;
                            state = 23;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6476_);
                            leanh::lean_dec(v___x_6444_);
                            v___x_6478_ = leanh::lean_box(0);
                            v_isShared_6479_ = v_isSharedCheck_6483_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6442_);
                    leanh::lean_dec(v_stx_6353_);
                    return v___y_6441_;
                }
            }
            17 => {
                v___x_6452_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10;
                v___x_6453_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(
                    leanh::lean_box(0),
                    v___x_6452_,
                    v___f_6394_,
                    v_a_6448_,
                );
                if v_isShared_6451_ == 0 {
                    leanh::lean_ctor_set(v___x_6450_, 0, v___x_6453_);
                    v___x_6455_ = v___x_6450_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6456_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6456_, 0, v___x_6453_);
                    v___x_6455_ = v_reuseFailAlloc_6456_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6455_;
            }
            19 => {
                leanh::lean_inc(v_a_6458_);
                if v_isShared_6461_ == 0 {
                    v___x_6463_ = v___x_6460_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6466_, 0, v_a_6458_);
                    v___x_6463_ = v_reuseFailAlloc_6466_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_6464_ = l_Lean_Exception_isInterrupt(v_a_6458_);
                if v___x_6464_ == 0 {
                    v___x_6465_ = l_Lean_Exception_isRuntime(v_a_6458_);
                    v___y_6397_ = v___x_6463_;
                    v___y_6398_ = v_a_6446_;
                    v___y_6399_ = v___x_6465_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6458_);
                    v___y_6397_ = v___x_6463_;
                    v___y_6398_ = v_a_6446_;
                    v___y_6399_ = v___x_6464_;
                    state = 7;
                    continue;
                }
            }
            21 => {
                if v_isShared_6471_ == 0 {
                    v___x_6473_ = v___x_6470_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6474_, 0, v_a_6468_);
                    v___x_6473_ = v_reuseFailAlloc_6474_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6473_;
            }
            23 => {
                if v_isShared_6479_ == 0 {
                    v___x_6481_ = v___x_6478_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6482_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6482_, 0, v_a_6476_);
                    v___x_6481_ = v_reuseFailAlloc_6482_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6481_;
            }
            25 => {
                if v___y_6488_ == 0 {
                    leanh::lean_dec_ref(v___y_6486_);
                    v___x_6489_ =
                        l_Lean_Meta_SavedState_restore___redArg(v___y_6487_, v_a_6357_, v_a_6359_);
                    leanh::lean_dec_ref(v___y_6487_);
                    if leanh::lean_obj_tag(v___x_6489_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6489_, 1);
                        v___x_6490_ = l_Lean_Meta_saveState___redArg(v_a_6357_, v_a_6359_);
                        if leanh::lean_obj_tag(v___x_6490_) == 0 {
                            v_a_6491_ = leanh::lean_ctor_get(v___x_6490_, 0);
                            leanh::lean_inc(v_a_6491_);
                            leanh::lean_dec_ref_known(v___x_6490_, 1);
                            leanh::lean_inc(v_stx_6353_);
                            v___x_6492_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx(
                                v_stx_6353_,
                                v_a_6354_,
                                v_a_6355_,
                                v_a_6356_,
                                v_a_6357_,
                                v_a_6358_,
                                v_a_6359_,
                            );
                            if leanh::lean_obj_tag(v___x_6492_) == 0 {
                                leanh::lean_dec(v_a_6491_);
                                leanh::lean_dec(v_stx_6353_);
                                v_a_6493_ = leanh::lean_ctor_get(v___x_6492_, 0);
                                v_isSharedCheck_6502_ =
                                    (!leanh::lean_is_exclusive(v___x_6492_)) as u8;
                                if v_isSharedCheck_6502_ == 0 {
                                    v___x_6495_ = v___x_6492_;
                                    v_isShared_6496_ = v_isSharedCheck_6502_;
                                    state = 26;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6493_);
                                    leanh::lean_dec(v___x_6492_);
                                    v___x_6495_ = leanh::lean_box(0);
                                    v_isShared_6496_ = v_isSharedCheck_6502_;
                                    state = 26;
                                    continue;
                                }
                            } else {
                                v_a_6503_ = leanh::lean_ctor_get(v___x_6492_, 0);
                                v_isSharedCheck_6512_ =
                                    (!leanh::lean_is_exclusive(v___x_6492_)) as u8;
                                if v_isSharedCheck_6512_ == 0 {
                                    v___x_6505_ = v___x_6492_;
                                    v_isShared_6506_ = v_isSharedCheck_6512_;
                                    state = 28;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6503_);
                                    leanh::lean_dec(v___x_6492_);
                                    v___x_6505_ = leanh::lean_box(0);
                                    v_isShared_6506_ = v_isSharedCheck_6512_;
                                    state = 28;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_stx_6353_);
                            v_a_6513_ = leanh::lean_ctor_get(v___x_6490_, 0);
                            v_isSharedCheck_6520_ =
                                (!leanh::lean_is_exclusive(v___x_6490_)) as u8;
                            if v_isSharedCheck_6520_ == 0 {
                                v___x_6515_ = v___x_6490_;
                                v_isShared_6516_ = v_isSharedCheck_6520_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6513_);
                                leanh::lean_dec(v___x_6490_);
                                v___x_6515_ = leanh::lean_box(0);
                                v_isShared_6516_ = v_isSharedCheck_6520_;
                                state = 30;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_stx_6353_);
                        v_a_6521_ = leanh::lean_ctor_get(v___x_6489_, 0);
                        v_isSharedCheck_6528_ =
                            (!leanh::lean_is_exclusive(v___x_6489_)) as u8;
                        if v_isSharedCheck_6528_ == 0 {
                            v___x_6523_ = v___x_6489_;
                            v_isShared_6524_ = v_isSharedCheck_6528_;
                            state = 32;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6521_);
                            leanh::lean_dec(v___x_6489_);
                            v___x_6523_ = leanh::lean_box(0);
                            v_isShared_6524_ = v_isSharedCheck_6528_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6487_);
                    leanh::lean_dec(v_stx_6353_);
                    return v___y_6486_;
                }
            }
            26 => {
                v___x_6497_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13;
                v___x_6498_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(
                    leanh::lean_box(0),
                    v___x_6497_,
                    v___f_6484_,
                    v_a_6493_,
                );
                if v_isShared_6496_ == 0 {
                    leanh::lean_ctor_set(v___x_6495_, 0, v___x_6498_);
                    v___x_6500_ = v___x_6495_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6501_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6501_, 0, v___x_6498_);
                    v___x_6500_ = v_reuseFailAlloc_6501_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6500_;
            }
            28 => {
                leanh::lean_inc(v_a_6503_);
                if v_isShared_6506_ == 0 {
                    v___x_6508_ = v___x_6505_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6511_, 0, v_a_6503_);
                    v___x_6508_ = v_reuseFailAlloc_6511_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                v___x_6509_ = l_Lean_Exception_isInterrupt(v_a_6503_);
                if v___x_6509_ == 0 {
                    v___x_6510_ = l_Lean_Exception_isRuntime(v_a_6503_);
                    v___y_6441_ = v___x_6508_;
                    v___y_6442_ = v_a_6491_;
                    v___y_6443_ = v___x_6510_;
                    state = 16;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6503_);
                    v___y_6441_ = v___x_6508_;
                    v___y_6442_ = v_a_6491_;
                    v___y_6443_ = v___x_6509_;
                    state = 16;
                    continue;
                }
            }
            30 => {
                if v_isShared_6516_ == 0 {
                    v___x_6518_ = v___x_6515_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6519_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6519_, 0, v_a_6513_);
                    v___x_6518_ = v_reuseFailAlloc_6519_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_6518_;
            }
            32 => {
                if v_isShared_6524_ == 0 {
                    v___x_6526_ = v___x_6523_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_6527_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6521_);
                    v___x_6526_ = v_reuseFailAlloc_6527_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_6526_;
            }
            34 => {
                v___x_6573_ = l_Lean_Exception_isInterrupt(v_a_6389_);
                if v___x_6573_ == 0 {
                    v___x_6574_ = l_Lean_Exception_isRuntime(v_a_6389_);
                    v___y_6532_ = v___x_6574_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6389_);
                    v___y_6532_ = v___x_6573_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v___y_6532_ == 0 {
                    leanh::lean_dec_ref(v___x_6530_);
                    v___x_6533_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_6376_, v_a_6357_, v_a_6359_);
                    leanh::lean_dec(v_a_6376_);
                    if leanh::lean_obj_tag(v___x_6533_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6533_, 1);
                        v___x_6534_ = l_Lean_Meta_saveState___redArg(v_a_6357_, v_a_6359_);
                        if leanh::lean_obj_tag(v___x_6534_) == 0 {
                            v_a_6535_ = leanh::lean_ctor_get(v___x_6534_, 0);
                            leanh::lean_inc(v_a_6535_);
                            leanh::lean_dec_ref_known(v___x_6534_, 1);
                            leanh::lean_inc(v_stx_6353_);
                            v___x_6536_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx(
                                v_stx_6353_,
                                v_a_6354_,
                                v_a_6355_,
                                v_a_6356_,
                                v_a_6357_,
                                v_a_6358_,
                                v_a_6359_,
                            );
                            if leanh::lean_obj_tag(v___x_6536_) == 0 {
                                leanh::lean_dec(v_a_6535_);
                                leanh::lean_dec(v_stx_6353_);
                                v_a_6537_ = leanh::lean_ctor_get(v___x_6536_, 0);
                                v_isSharedCheck_6546_ =
                                    (!leanh::lean_is_exclusive(v___x_6536_)) as u8;
                                if v_isSharedCheck_6546_ == 0 {
                                    v___x_6539_ = v___x_6536_;
                                    v_isShared_6540_ = v_isSharedCheck_6546_;
                                    state = 36;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6537_);
                                    leanh::lean_dec(v___x_6536_);
                                    v___x_6539_ = leanh::lean_box(0);
                                    v_isShared_6540_ = v_isSharedCheck_6546_;
                                    state = 36;
                                    continue;
                                }
                            } else {
                                v_a_6547_ = leanh::lean_ctor_get(v___x_6536_, 0);
                                v_isSharedCheck_6556_ =
                                    (!leanh::lean_is_exclusive(v___x_6536_)) as u8;
                                if v_isSharedCheck_6556_ == 0 {
                                    v___x_6549_ = v___x_6536_;
                                    v_isShared_6550_ = v_isSharedCheck_6556_;
                                    state = 38;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6547_);
                                    leanh::lean_dec(v___x_6536_);
                                    v___x_6549_ = leanh::lean_box(0);
                                    v_isShared_6550_ = v_isSharedCheck_6556_;
                                    state = 38;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_stx_6353_);
                            v_a_6557_ = leanh::lean_ctor_get(v___x_6534_, 0);
                            v_isSharedCheck_6564_ =
                                (!leanh::lean_is_exclusive(v___x_6534_)) as u8;
                            if v_isSharedCheck_6564_ == 0 {
                                v___x_6559_ = v___x_6534_;
                                v_isShared_6560_ = v_isSharedCheck_6564_;
                                state = 40;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6557_);
                                leanh::lean_dec(v___x_6534_);
                                v___x_6559_ = leanh::lean_box(0);
                                v_isShared_6560_ = v_isSharedCheck_6564_;
                                state = 40;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_stx_6353_);
                        v_a_6565_ = leanh::lean_ctor_get(v___x_6533_, 0);
                        v_isSharedCheck_6572_ =
                            (!leanh::lean_is_exclusive(v___x_6533_)) as u8;
                        if v_isSharedCheck_6572_ == 0 {
                            v___x_6567_ = v___x_6533_;
                            v_isShared_6568_ = v_isSharedCheck_6572_;
                            state = 42;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6565_);
                            leanh::lean_dec(v___x_6533_);
                            v___x_6567_ = leanh::lean_box(0);
                            v_isShared_6568_ = v_isSharedCheck_6572_;
                            state = 42;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6376_);
                    leanh::lean_dec(v_stx_6353_);
                    return v___x_6530_;
                }
            }
            36 => {
                v___x_6541_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15;
                v___x_6542_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___lam__0(
                    leanh::lean_box(0),
                    v___x_6541_,
                    v___f_6393_,
                    v_a_6537_,
                );
                if v_isShared_6540_ == 0 {
                    leanh::lean_ctor_set(v___x_6539_, 0, v___x_6542_);
                    v___x_6544_ = v___x_6539_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6545_, 0, v___x_6542_);
                    v___x_6544_ = v_reuseFailAlloc_6545_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6544_;
            }
            38 => {
                leanh::lean_inc(v_a_6547_);
                if v_isShared_6550_ == 0 {
                    v___x_6552_ = v___x_6549_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6555_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6555_, 0, v_a_6547_);
                    v___x_6552_ = v_reuseFailAlloc_6555_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                v___x_6553_ = l_Lean_Exception_isInterrupt(v_a_6547_);
                if v___x_6553_ == 0 {
                    v___x_6554_ = l_Lean_Exception_isRuntime(v_a_6547_);
                    v___y_6486_ = v___x_6552_;
                    v___y_6487_ = v_a_6535_;
                    v___y_6488_ = v___x_6554_;
                    state = 25;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6547_);
                    v___y_6486_ = v___x_6552_;
                    v___y_6487_ = v_a_6535_;
                    v___y_6488_ = v___x_6553_;
                    state = 25;
                    continue;
                }
            }
            40 => {
                if v_isShared_6560_ == 0 {
                    v___x_6562_ = v___x_6559_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6563_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6563_, 0, v_a_6557_);
                    v___x_6562_ = v_reuseFailAlloc_6563_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6562_;
            }
            42 => {
                if v_isShared_6568_ == 0 {
                    v___x_6570_ = v___x_6567_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_6571_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6571_, 0, v_a_6565_);
                    v___x_6570_ = v_reuseFailAlloc_6571_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_6570_;
            }
            44 => {
                if v_isShared_6580_ == 0 {
                    v___x_6582_ = v___x_6579_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_6583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6583_, 0, v_a_6577_);
                    v___x_6582_ = v_reuseFailAlloc_6583_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_6582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___boxed(
    mut v_stx_6585_: *mut leanh::LeanObject,
    mut v_a_6586_: *mut leanh::LeanObject,
    mut v_a_6587_: *mut leanh::LeanObject,
    mut v_a_6588_: *mut leanh::LeanObject,
    mut v_a_6589_: *mut leanh::LeanObject,
    mut v_a_6590_: *mut leanh::LeanObject,
    mut v_a_6591_: *mut leanh::LeanObject,
    mut v_a_6592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6593_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx(
        v_stx_6585_,
        v_a_6586_,
        v_a_6587_,
        v_a_6588_,
        v_a_6589_,
        v_a_6590_,
        v_a_6591_,
    );
    leanh::lean_dec(v_a_6591_);
    leanh::lean_dec_ref(v_a_6590_);
    leanh::lean_dec(v_a_6589_);
    leanh::lean_dec_ref(v_a_6588_);
    leanh::lean_dec(v_a_6587_);
    leanh::lean_dec_ref(v_a_6586_);
    return v_res_6593_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6595_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__2,
    );
    v___x_6596_ = l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__0;
    v___x_6597_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6597_, 0, v___x_6596_);
    leanh::lean_ctor_set(v___x_6597_, 1, v___x_6595_);
    return v___x_6597_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool() -> *mut leanh::LeanObject {
    let mut v___x_6598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6598_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool___closed__1,
    );
    return v___x_6598_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6600_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__2,
    );
    v___x_6601_ = l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__0;
    v___x_6602_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6602_, 0, v___x_6601_);
    leanh::lean_ctor_set(v___x_6602_, 1, v___x_6600_);
    return v___x_6602_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat() -> *mut leanh::LeanObject {
    let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6603_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat___closed__1,
    );
    return v___x_6603_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6605_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__2,
    );
    v___x_6606_ = l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__0;
    v___x_6607_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6607_, 0, v___x_6606_);
    leanh::lean_ctor_set(v___x_6607_, 1, v___x_6605_);
    return v___x_6607_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt() -> *mut leanh::LeanObject {
    let mut v___x_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6608_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt___closed__1,
    );
    return v___x_6608_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6610_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__2,
    );
    v___x_6611_ = l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__0;
    v___x_6612_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6612_, 0, v___x_6611_);
    leanh::lean_ctor_set(v___x_6612_, 1, v___x_6610_);
    return v___x_6612_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instString() -> *mut leanh::LeanObject {
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6613_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instString___closed__1,
    );
    return v___x_6613_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6615_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__2,
    );
    v___x_6616_ = l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__0;
    v___x_6617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6617_, 0, v___x_6616_);
    leanh::lean_ctor_set(v___x_6617_, 1, v___x_6615_);
    return v___x_6617_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instName() -> *mut leanh::LeanObject {
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6618_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instName___closed__1,
    );
    return v___x_6618_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(
    mut v_inst_6619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalTerm_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeExpr_6621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6624_: u8 = 0;
    let mut v___x_6625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_6620_ = leanh::lean_ctor_get(v_inst_6619_, 0);
                v_typeExpr_6621_ = leanh::lean_ctor_get(v_inst_6619_, 1);
                v_isSharedCheck_6631_ = (!leanh::lean_is_exclusive(v_inst_6619_)) as u8;
                if v_isSharedCheck_6631_ == 0 {
                    v___x_6623_ = v_inst_6619_;
                    v_isShared_6624_ = v_isSharedCheck_6631_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeExpr_6621_);
                    leanh::lean_inc(v_evalTerm_6620_);
                    leanh::lean_dec(v_inst_6619_);
                    v___x_6623_ = leanh::lean_box(0);
                    v_isShared_6624_ = v_isSharedCheck_6631_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_typeExpr_6621_);
                v___x_6625_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                leanh::lean_closure_set(v___x_6625_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6625_, 1, v_typeExpr_6621_);
                leanh::lean_closure_set(v___x_6625_, 2, v_evalTerm_6620_);
                v___x_6626_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2,
                );
                v___x_6627_ = l_Lean_Expr_app___override(v___x_6626_, v_typeExpr_6621_);
                if v_isShared_6624_ == 0 {
                    leanh::lean_ctor_set(v___x_6623_, 1, v___x_6627_);
                    leanh::lean_ctor_set(v___x_6623_, 0, v___x_6625_);
                    v___x_6629_ = v___x_6623_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6630_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6630_, 0, v___x_6625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6630_, 1, v___x_6627_);
                    v___x_6629_ = v_reuseFailAlloc_6630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instOption(
    mut v_00_u03b1_6632_: *mut leanh::LeanObject,
    mut v_inst_6633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6634_ = l_Lean_Elab_ConfigEval_EvalTerm_instOption___redArg(v_inst_6633_);
    return v___x_6634_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(
    mut v_inst_6635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalTerm_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeExpr_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6640_: u8 = 0;
    let mut v___x_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_6636_ = leanh::lean_ctor_get(v_inst_6635_, 0);
                v_typeExpr_6637_ = leanh::lean_ctor_get(v_inst_6635_, 1);
                v_isSharedCheck_6647_ = (!leanh::lean_is_exclusive(v_inst_6635_)) as u8;
                if v_isSharedCheck_6647_ == 0 {
                    v___x_6639_ = v_inst_6635_;
                    v_isShared_6640_ = v_isSharedCheck_6647_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeExpr_6637_);
                    leanh::lean_inc(v_evalTerm_6636_);
                    leanh::lean_dec(v_inst_6635_);
                    v___x_6639_ = leanh::lean_box(0);
                    v_isShared_6640_ = v_isSharedCheck_6647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_typeExpr_6637_);
                v___x_6641_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                leanh::lean_closure_set(v___x_6641_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6641_, 1, v_typeExpr_6637_);
                leanh::lean_closure_set(v___x_6641_, 2, v_evalTerm_6636_);
                v___x_6642_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1,
                );
                v___x_6643_ = l_Lean_Expr_app___override(v___x_6642_, v_typeExpr_6637_);
                if v_isShared_6640_ == 0 {
                    leanh::lean_ctor_set(v___x_6639_, 1, v___x_6643_);
                    leanh::lean_ctor_set(v___x_6639_, 0, v___x_6641_);
                    v___x_6645_ = v___x_6639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6646_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6646_, 0, v___x_6641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6646_, 1, v___x_6643_);
                    v___x_6645_ = v_reuseFailAlloc_6646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instList(
    mut v_00_u03b1_6648_: *mut leanh::LeanObject,
    mut v_inst_6649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6650_ = l_Lean_Elab_ConfigEval_EvalTerm_instList___redArg(v_inst_6649_);
    return v___x_6650_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(
    mut v_inst_6651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalTerm_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeExpr_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6656_: u8 = 0;
    let mut v___x_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_6652_ = leanh::lean_ctor_get(v_inst_6651_, 0);
                v_typeExpr_6653_ = leanh::lean_ctor_get(v_inst_6651_, 1);
                v_isSharedCheck_6663_ = (!leanh::lean_is_exclusive(v_inst_6651_)) as u8;
                if v_isSharedCheck_6663_ == 0 {
                    v___x_6655_ = v_inst_6651_;
                    v_isShared_6656_ = v_isSharedCheck_6663_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeExpr_6653_);
                    leanh::lean_inc(v_evalTerm_6652_);
                    leanh::lean_dec(v_inst_6651_);
                    v___x_6655_ = leanh::lean_box(0);
                    v_isShared_6656_ = v_isSharedCheck_6663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_typeExpr_6653_);
                v___x_6657_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___boxed as *mut core::ffi::c_void,
                    11,
                    3,
                );
                leanh::lean_closure_set(v___x_6657_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6657_, 1, v_typeExpr_6653_);
                leanh::lean_closure_set(v___x_6657_, 2, v_evalTerm_6652_);
                v___x_6658_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2,
                );
                v___x_6659_ = l_Lean_Expr_app___override(v___x_6658_, v_typeExpr_6653_);
                if v_isShared_6656_ == 0 {
                    leanh::lean_ctor_set(v___x_6655_, 1, v___x_6659_);
                    leanh::lean_ctor_set(v___x_6655_, 0, v___x_6657_);
                    v___x_6661_ = v___x_6655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6662_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6662_, 0, v___x_6657_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6662_, 1, v___x_6659_);
                    v___x_6661_ = v_reuseFailAlloc_6662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instArray(
    mut v_00_u03b1_6664_: *mut leanh::LeanObject,
    mut v_inst_6665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6666_ = l_Lean_Elab_ConfigEval_EvalTerm_instArray___redArg(v_inst_6665_);
    return v___x_6666_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(
    mut v_inst_6667_: *mut leanh::LeanObject,
    mut v_inst_6668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalTerm_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeExpr_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_evalTerm_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeExpr_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6675_: u8 = 0;
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalTerm_6669_ = leanh::lean_ctor_get(v_inst_6667_, 0);
                leanh::lean_inc_ref(v_evalTerm_6669_);
                v_typeExpr_6670_ = leanh::lean_ctor_get(v_inst_6667_, 1);
                leanh::lean_inc_ref(v_typeExpr_6670_);
                leanh::lean_dec_ref(v_inst_6667_);
                v_evalTerm_6671_ = leanh::lean_ctor_get(v_inst_6668_, 0);
                v_typeExpr_6672_ = leanh::lean_ctor_get(v_inst_6668_, 1);
                v_isSharedCheck_6682_ = (!leanh::lean_is_exclusive(v_inst_6668_)) as u8;
                if v_isSharedCheck_6682_ == 0 {
                    v___x_6674_ = v_inst_6668_;
                    v_isShared_6675_ = v_isSharedCheck_6682_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_typeExpr_6672_);
                    leanh::lean_inc(v_evalTerm_6671_);
                    leanh::lean_dec(v_inst_6668_);
                    v___x_6674_ = leanh::lean_box(0);
                    v_isShared_6675_ = v_isSharedCheck_6682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_typeExpr_6672_);
                leanh::lean_inc_ref(v_typeExpr_6670_);
                v___x_6676_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___boxed as *mut core::ffi::c_void,
                    14,
                    6,
                );
                leanh::lean_closure_set(v___x_6676_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6676_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_6676_, 2, v_typeExpr_6670_);
                leanh::lean_closure_set(v___x_6676_, 3, v_typeExpr_6672_);
                leanh::lean_closure_set(v___x_6676_, 4, v_evalTerm_6669_);
                leanh::lean_closure_set(v___x_6676_, 5, v_evalTerm_6671_);
                v___x_6677_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalProdStx___redArg___closed__3,
                );
                v___x_6678_ = l_Lean_mkAppB(v___x_6677_, v_typeExpr_6670_, v_typeExpr_6672_);
                if v_isShared_6675_ == 0 {
                    leanh::lean_ctor_set(v___x_6674_, 1, v___x_6678_);
                    leanh::lean_ctor_set(v___x_6674_, 0, v___x_6676_);
                    v___x_6680_ = v___x_6674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6681_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6681_, 0, v___x_6676_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6681_, 1, v___x_6678_);
                    v___x_6680_ = v_reuseFailAlloc_6681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalTerm_instProd(
    mut v_00_u03b1_6683_: *mut leanh::LeanObject,
    mut v_00_u03b1_x27_6684_: *mut leanh::LeanObject,
    mut v_inst_6685_: *mut leanh::LeanObject,
    mut v_inst_6686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6687_ = l_Lean_Elab_ConfigEval_EvalTerm_instProd___redArg(v_inst_6685_, v_inst_6686_);
    return v___x_6687_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6692_ = leanh::lean_box(0);
    v___x_6693_ = l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1;
    v___x_6694_ = l_Lean_Expr_const___override(v___x_6693_, v___x_6692_);
    return v___x_6694_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6695_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__2,
    );
    v___x_6696_ = l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__0;
    v___x_6697_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6697_, 0, v___x_6696_);
    leanh::lean_ctor_set(v___x_6697_, 1, v___x_6695_);
    return v___x_6697_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue() -> *mut leanh::LeanObject
{
    let mut v___x_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6698_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__3,
    );
    return v___x_6698_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6699_ = leanh::lean_box(0);
    v___x_6700_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_6701_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6701_, 0, v___x_6700_);
    leanh::lean_ctor_set(v___x_6701_, 1, v___x_6699_);
    return v___x_6701_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6703_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___closed__0);
    v___x_6704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6704_, 0, v___x_6703_);
    return v___x_6704_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg___boxed(
    mut v___y_6705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6706_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
    return v_res_6706_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(
    mut v_00_u03b1_6707_: *mut leanh::LeanObject,
    mut v___y_6708_: *mut leanh::LeanObject,
    mut v___y_6709_: *mut leanh::LeanObject,
    mut v___y_6710_: *mut leanh::LeanObject,
    mut v___y_6711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6713_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
    return v___x_6713_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___boxed(
    mut v_00_u03b1_6714_: *mut leanh::LeanObject,
    mut v___y_6715_: *mut leanh::LeanObject,
    mut v___y_6716_: *mut leanh::LeanObject,
    mut v___y_6717_: *mut leanh::LeanObject,
    mut v___y_6718_: *mut leanh::LeanObject,
    mut v___y_6719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6720_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0(v_00_u03b1_6714_, v___y_6715_, v___y_6716_, v___y_6717_, v___y_6718_);
    leanh::lean_dec(v___y_6718_);
    leanh::lean_dec_ref(v___y_6717_);
    leanh::lean_dec(v___y_6716_);
    leanh::lean_dec_ref(v___y_6715_);
    return v_res_6720_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(
    mut v_e_6721_: *mut leanh::LeanObject,
    mut v_a_6722_: *mut leanh::LeanObject,
    mut v_a_6723_: *mut leanh::LeanObject,
    mut v_a_6724_: *mut leanh::LeanObject,
    mut v_a_6725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: u8 = 0;
    v___x_6727_ = l_Lean_Expr_cleanupAnnotations(v_e_6721_);
    v___x_6728_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__8;
    v___x_6729_ = l_Lean_Expr_isConstOf(v___x_6727_, v___x_6728_);
    if v___x_6729_ == 0 {
        let mut v___x_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6731_: u8 = 0;
        v___x_6730_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__5;
        v___x_6731_ = l_Lean_Expr_isConstOf(v___x_6727_, v___x_6730_);
        leanh::lean_dec_ref(v___x_6727_);
        if v___x_6731_ == 0 {
            let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6732_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
            return v___x_6732_;
        } else {
            let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_6733_ = leanh::lean_box((v___x_6731_) as usize);
            v___x_6734_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_6734_, 0, v___x_6733_);
            return v___x_6734_;
        }
    } else {
        let mut v___x_6735_: u8 = 0;
        let mut v___x_6736_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6737_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_6727_);
        v___x_6735_ = 0;
        v___x_6736_ = leanh::lean_box((v___x_6735_) as usize);
        v___x_6737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6737_, 0, v___x_6736_);
        return v___x_6737_;
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore___boxed(
    mut v_e_6738_: *mut leanh::LeanObject,
    mut v_a_6739_: *mut leanh::LeanObject,
    mut v_a_6740_: *mut leanh::LeanObject,
    mut v_a_6741_: *mut leanh::LeanObject,
    mut v_a_6742_: *mut leanh::LeanObject,
    mut v_a_6743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6744_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(
        v_e_6738_, v_a_6739_, v_a_6740_, v_a_6741_, v_a_6742_,
    );
    leanh::lean_dec(v_a_6742_);
    leanh::lean_dec_ref(v_a_6741_);
    leanh::lean_dec(v_a_6740_);
    leanh::lean_dec_ref(v_a_6739_);
    return v_res_6744_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6747_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__1;
    v___x_6748_ = l_Lean_stringToMessageData(v___x_6747_);
    return v___x_6748_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6749_: u8 = 0;
    let mut v___x_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6749_ = 0;
    v___x_6750_ = l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__1;
    v___x_6751_ = l_Lean_MessageData_ofConstName(v___x_6750_, v___x_6749_);
    return v___x_6751_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6752_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__3,
    );
    v___x_6753_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_6754_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6754_, 0, v___x_6753_);
    leanh::lean_ctor_set(v___x_6754_, 1, v___x_6752_);
    return v___x_6754_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_6756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6756_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__5;
    v___x_6757_ = l_Lean_stringToMessageData(v___x_6756_);
    return v___x_6757_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6758_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_6759_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__4,
    );
    v___x_6760_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6760_, 0, v___x_6759_);
    leanh::lean_ctor_set(v___x_6760_, 1, v___x_6758_);
    return v___x_6760_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
    mut v_e_6761_: *mut leanh::LeanObject,
    mut v_a_6762_: *mut leanh::LeanObject,
    mut v_a_6763_: *mut leanh::LeanObject,
    mut v_a_6764_: *mut leanh::LeanObject,
    mut v_a_6765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6767_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__0;
    v___x_6768_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__7,
    );
    v___x_6769_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___x_6767_,
        v_e_6761_,
        v___x_6768_,
        v_a_6762_,
        v_a_6763_,
        v_a_6764_,
        v_a_6765_,
    );
    return v___x_6769_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___boxed(
    mut v_e_6770_: *mut leanh::LeanObject,
    mut v_a_6771_: *mut leanh::LeanObject,
    mut v_a_6772_: *mut leanh::LeanObject,
    mut v_a_6773_: *mut leanh::LeanObject,
    mut v_a_6774_: *mut leanh::LeanObject,
    mut v_a_6775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6776_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
        v_e_6770_, v_a_6771_, v_a_6772_, v_a_6773_, v_a_6774_,
    );
    leanh::lean_dec(v_a_6774_);
    leanh::lean_dec_ref(v_a_6773_);
    leanh::lean_dec(v_a_6772_);
    leanh::lean_dec_ref(v_a_6771_);
    return v_res_6776_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(
    mut v_e_6777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6785_: u8 = 0;
    let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6789_: u8 = 0;
    let mut v___x_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_6777_);
                v___x_6790_ = l_Lean_Expr_nat_x3f(v_e_6777_);
                if leanh::lean_obj_tag(v___x_6790_) == 0 {
                    v___x_6791_ = l_Lean_Expr_rawNatLit_x3f(v_e_6777_);
                    v___y_6780_ = v___x_6791_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_e_6777_);
                    v___y_6780_ = v___x_6790_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_6780_) == 0 {
                    v___x_6781_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                    return v___x_6781_;
                } else {
                    v_val_6782_ = leanh::lean_ctor_get(v___y_6780_, 0);
                    v_isSharedCheck_6789_ = (!leanh::lean_is_exclusive(v___y_6780_)) as u8;
                    if v_isSharedCheck_6789_ == 0 {
                        v___x_6784_ = v___y_6780_;
                        v_isShared_6785_ = v_isSharedCheck_6789_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6782_);
                        leanh::lean_dec(v___y_6780_);
                        v___x_6784_ = leanh::lean_box(0);
                        v_isShared_6785_ = v_isSharedCheck_6789_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6785_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6784_, 0);
                    v___x_6787_ = v___x_6784_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6788_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6788_, 0, v_val_6782_);
                    v___x_6787_ = v_reuseFailAlloc_6788_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg___boxed(
    mut v_e_6792_: *mut leanh::LeanObject,
    mut v_a_6793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6794_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_6792_);
    return v_res_6794_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(
    mut v_e_6795_: *mut leanh::LeanObject,
    mut v_a_6796_: *mut leanh::LeanObject,
    mut v_a_6797_: *mut leanh::LeanObject,
    mut v_a_6798_: *mut leanh::LeanObject,
    mut v_a_6799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6801_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_6795_);
    return v___x_6801_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___boxed(
    mut v_e_6802_: *mut leanh::LeanObject,
    mut v_a_6803_: *mut leanh::LeanObject,
    mut v_a_6804_: *mut leanh::LeanObject,
    mut v_a_6805_: *mut leanh::LeanObject,
    mut v_a_6806_: *mut leanh::LeanObject,
    mut v_a_6807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6808_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore(
        v_e_6802_, v_a_6803_, v_a_6804_, v_a_6805_, v_a_6806_,
    );
    leanh::lean_dec(v_a_6806_);
    leanh::lean_dec_ref(v_a_6805_);
    leanh::lean_dec(v_a_6804_);
    leanh::lean_dec_ref(v_a_6803_);
    return v_res_6808_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6810_: u8 = 0;
    let mut v___x_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6810_ = 0;
    v___x_6811_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__1;
    v___x_6812_ = l_Lean_MessageData_ofConstName(v___x_6811_, v___x_6810_);
    return v___x_6812_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6813_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__1,
    );
    v___x_6814_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_6815_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6815_, 0, v___x_6814_);
    leanh::lean_ctor_set(v___x_6815_, 1, v___x_6813_);
    return v___x_6815_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6816_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_6817_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__2,
    );
    v___x_6818_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6818_, 0, v___x_6817_);
    leanh::lean_ctor_set(v___x_6818_, 1, v___x_6816_);
    return v___x_6818_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(
    mut v_e_6819_: *mut leanh::LeanObject,
    mut v_a_6820_: *mut leanh::LeanObject,
    mut v_a_6821_: *mut leanh::LeanObject,
    mut v_a_6822_: *mut leanh::LeanObject,
    mut v_a_6823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6825_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__0;
    v___x_6826_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___closed__3,
    );
    v___x_6827_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___x_6825_,
        v_e_6819_,
        v___x_6826_,
        v_a_6820_,
        v_a_6821_,
        v_a_6822_,
        v_a_6823_,
    );
    return v___x_6827_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr___boxed(
    mut v_e_6828_: *mut leanh::LeanObject,
    mut v_a_6829_: *mut leanh::LeanObject,
    mut v_a_6830_: *mut leanh::LeanObject,
    mut v_a_6831_: *mut leanh::LeanObject,
    mut v_a_6832_: *mut leanh::LeanObject,
    mut v_a_6833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6834_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(
        v_e_6828_, v_a_6829_, v_a_6830_, v_a_6831_, v_a_6832_,
    );
    leanh::lean_dec(v_a_6832_);
    leanh::lean_dec_ref(v_a_6831_);
    leanh::lean_dec(v_a_6830_);
    leanh::lean_dec_ref(v_a_6829_);
    return v_res_6834_;
}
pub unsafe fn l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(
    mut v_msg_6835_: *mut leanh::LeanObject,
    mut v___y_6836_: *mut leanh::LeanObject,
    mut v___y_6837_: *mut leanh::LeanObject,
    mut v___y_6838_: *mut leanh::LeanObject,
    mut v___y_6839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6846_: u8 = 0;
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6841_ = leanh::lean_ctor_get(v___y_6838_, 5);
                v___x_6842_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ConfigEval_EvalTerm_evalNameStx_spec__0_spec__0_spec__2_spec__6(v_msg_6835_, v___y_6836_, v___y_6837_, v___y_6838_, v___y_6839_);
                v_a_6843_ = leanh::lean_ctor_get(v___x_6842_, 0);
                v_isSharedCheck_6851_ = (!leanh::lean_is_exclusive(v___x_6842_)) as u8;
                if v_isSharedCheck_6851_ == 0 {
                    v___x_6845_ = v___x_6842_;
                    v_isShared_6846_ = v_isSharedCheck_6851_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6843_);
                    leanh::lean_dec(v___x_6842_);
                    v___x_6845_ = leanh::lean_box(0);
                    v_isShared_6846_ = v_isSharedCheck_6851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_6841_);
                v___x_6847_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6847_, 0, v_ref_6841_);
                leanh::lean_ctor_set(v___x_6847_, 1, v_a_6843_);
                if v_isShared_6846_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6845_, 1);
                    leanh::lean_ctor_set(v___x_6845_, 0, v___x_6847_);
                    v___x_6849_ = v___x_6845_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6850_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6850_, 0, v___x_6847_);
                    v___x_6849_ = v_reuseFailAlloc_6850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg___boxed(
    mut v_msg_6852_: *mut leanh::LeanObject,
    mut v___y_6853_: *mut leanh::LeanObject,
    mut v___y_6854_: *mut leanh::LeanObject,
    mut v___y_6855_: *mut leanh::LeanObject,
    mut v___y_6856_: *mut leanh::LeanObject,
    mut v___y_6857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6858_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_);
    leanh::lean_dec(v___y_6856_);
    leanh::lean_dec_ref(v___y_6855_);
    leanh::lean_dec(v___y_6854_);
    leanh::lean_dec_ref(v___y_6853_);
    return v_res_6858_;
}
pub unsafe fn _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6860_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__0;
    v___x_6861_ = l_Lean_stringToMessageData(v___x_6860_);
    return v___x_6861_;
}
pub unsafe fn l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(
    mut v_x_6862_: *mut leanh::LeanObject,
    mut v___y_6863_: *mut leanh::LeanObject,
    mut v___y_6864_: *mut leanh::LeanObject,
    mut v___y_6865_: *mut leanh::LeanObject,
    mut v___y_6866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6873_: u8 = 0;
    let mut v___x_6875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6862_) == 0 {
                    v___x_6868_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1_once), _init_l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___closed__1);
                    v___x_6869_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_6868_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_);
                    return v___x_6869_;
                } else {
                    v_val_6870_ = leanh::lean_ctor_get(v_x_6862_, 0);
                    v_isSharedCheck_6877_ = (!leanh::lean_is_exclusive(v_x_6862_)) as u8;
                    if v_isSharedCheck_6877_ == 0 {
                        v___x_6872_ = v_x_6862_;
                        v_isShared_6873_ = v_isSharedCheck_6877_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6870_);
                        leanh::lean_dec(v_x_6862_);
                        v___x_6872_ = leanh::lean_box(0);
                        v_isShared_6873_ = v_isSharedCheck_6877_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6873_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6872_, 0);
                    v___x_6875_ = v___x_6872_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6876_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6876_, 0, v_val_6870_);
                    v___x_6875_ = v_reuseFailAlloc_6876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg___boxed(
    mut v_x_6878_: *mut leanh::LeanObject,
    mut v___y_6879_: *mut leanh::LeanObject,
    mut v___y_6880_: *mut leanh::LeanObject,
    mut v___y_6881_: *mut leanh::LeanObject,
    mut v___y_6882_: *mut leanh::LeanObject,
    mut v___y_6883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6884_ =
        l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(
            v_x_6878_,
            v___y_6879_,
            v___y_6880_,
            v___y_6881_,
            v___y_6882_,
        );
    leanh::lean_dec(v___y_6882_);
    leanh::lean_dec_ref(v___y_6881_);
    leanh::lean_dec(v___y_6880_);
    leanh::lean_dec_ref(v___y_6879_);
    return v_res_6884_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(
    mut v_e_6892_: *mut leanh::LeanObject,
    mut v_a_6893_: *mut leanh::LeanObject,
    mut v_a_6894_: *mut leanh::LeanObject,
    mut v_a_6895_: *mut leanh::LeanObject,
    mut v_a_6896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6901_: u8 = 0;
    let mut v___x_6902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: u8 = 0;
    let mut v___x_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: u8 = 0;
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: u8 = 0;
    let mut v___x_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6917_: u8 = 0;
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6922_: u8 = 0;
    let mut v_a_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6926_: u8 = 0;
    let mut v___x_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6930_: u8 = 0;
    let mut v___x_6931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6935_: u8 = 0;
    let mut v___x_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6940_: u8 = 0;
    let mut v_a_6941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6944_: u8 = 0;
    let mut v___x_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6948_: u8 = 0;
    let mut v_a_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6952_: u8 = 0;
    let mut v___x_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6956_: u8 = 0;
    let mut v___x_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6963_: u8 = 0;
    let mut v___x_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6971_: u8 = 0;
    let mut v___x_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6976_: u8 = 0;
    let mut v_a_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6980_: u8 = 0;
    let mut v___x_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: u8 = 0;
    let mut v___x_6984_: u8 = 0;
    let mut v_reuseFailAlloc_6985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6986_: u8 = 0;
    let mut v_a_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6990_: u8 = 0;
    let mut v___x_6992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6994_: u8 = 0;
    let mut v_a_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6998_: u8 = 0;
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7002_: u8 = 0;
    let mut v___x_7003_: u8 = 0;
    let mut v___x_7004_: u8 = 0;
    let mut v_a_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7008_: u8 = 0;
    let mut v___x_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6957_ = l_Lean_Meta_saveState___redArg(v_a_6894_, v_a_6896_);
                if leanh::lean_obj_tag(v___x_6957_) == 0 {
                    v_a_6958_ = leanh::lean_ctor_get(v___x_6957_, 0);
                    leanh::lean_inc(v_a_6958_);
                    leanh::lean_dec_ref_known(v___x_6957_, 1);
                    leanh::lean_inc_ref(v_e_6892_);
                    v___x_6959_ = l_Lean_Expr_int_x3f(v_e_6892_);
                    v___x_6960_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(v___x_6959_, v_a_6893_, v_a_6894_, v_a_6895_, v_a_6896_);
                    if leanh::lean_obj_tag(v___x_6960_) == 0 {
                        leanh::lean_dec(v_a_6958_);
                        leanh::lean_dec_ref(v_e_6892_);
                        return v___x_6960_;
                    } else {
                        v_a_6961_ = leanh::lean_ctor_get(v___x_6960_, 0);
                        leanh::lean_inc(v_a_6961_);
                        v___x_7003_ = l_Lean_Exception_isInterrupt(v_a_6961_);
                        if v___x_7003_ == 0 {
                            v___x_7004_ = l_Lean_Exception_isRuntime(v_a_6961_);
                            v___y_6963_ = v___x_7004_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_6961_);
                            v___y_6963_ = v___x_7003_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6892_);
                    v_a_7005_ = leanh::lean_ctor_get(v___x_6957_, 0);
                    v_isSharedCheck_7012_ = (!leanh::lean_is_exclusive(v___x_6957_)) as u8;
                    if v_isSharedCheck_7012_ == 0 {
                        v___x_7007_ = v___x_6957_;
                        v_isShared_7008_ = v_isSharedCheck_7012_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7005_);
                        leanh::lean_dec(v___x_6957_);
                        v___x_7007_ = leanh::lean_box(0);
                        v_isShared_7008_ = v_isSharedCheck_7012_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6901_ == 0 {
                    leanh::lean_dec_ref(v___y_6900_);
                    v___x_6902_ =
                        l_Lean_Meta_SavedState_restore___redArg(v___y_6899_, v_a_6894_, v_a_6896_);
                    leanh::lean_dec_ref(v___y_6899_);
                    if leanh::lean_obj_tag(v___x_6902_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6902_, 1);
                        v___x_6903_ = l_Lean_Expr_cleanupAnnotations(v_e_6892_);
                        v___x_6904_ = l_Lean_Expr_isApp(v___x_6903_);
                        if v___x_6904_ == 0 {
                            leanh::lean_dec_ref(v___x_6903_);
                            v___x_6905_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                            return v___x_6905_;
                        } else {
                            v_arg_6906_ = leanh::lean_ctor_get(v___x_6903_, 1);
                            leanh::lean_inc_ref(v_arg_6906_);
                            v___x_6907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6903_);
                            v___x_6908_ =
                                l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__1;
                            v___x_6909_ = l_Lean_Expr_isConstOf(v___x_6907_, v___x_6908_);
                            if v___x_6909_ == 0 {
                                v___x_6910_ =
                                    l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___closed__2;
                                v___x_6911_ = l_Lean_Expr_isConstOf(v___x_6907_, v___x_6910_);
                                leanh::lean_dec_ref(v___x_6907_);
                                if v___x_6911_ == 0 {
                                    leanh::lean_dec_ref(v_arg_6906_);
                                    v___x_6912_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                                    return v___x_6912_;
                                } else {
                                    v___x_6913_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(
                                        v_arg_6906_,
                                        v_a_6893_,
                                        v_a_6894_,
                                        v_a_6895_,
                                        v_a_6896_,
                                    );
                                    if leanh::lean_obj_tag(v___x_6913_) == 0 {
                                        v_a_6914_ = leanh::lean_ctor_get(v___x_6913_, 0);
                                        v_isSharedCheck_6922_ =
                                            (!leanh::lean_is_exclusive(v___x_6913_)) as u8;
                                        if v_isSharedCheck_6922_ == 0 {
                                            v___x_6916_ = v___x_6913_;
                                            v_isShared_6917_ = v_isSharedCheck_6922_;
                                            state = 2;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6914_);
                                            leanh::lean_dec(v___x_6913_);
                                            v___x_6916_ = leanh::lean_box(0);
                                            v_isShared_6917_ = v_isSharedCheck_6922_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v_a_6923_ = leanh::lean_ctor_get(v___x_6913_, 0);
                                        v_isSharedCheck_6930_ =
                                            (!leanh::lean_is_exclusive(v___x_6913_)) as u8;
                                        if v_isSharedCheck_6930_ == 0 {
                                            v___x_6925_ = v___x_6913_;
                                            v_isShared_6926_ = v_isSharedCheck_6930_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6923_);
                                            leanh::lean_dec(v___x_6913_);
                                            v___x_6925_ = leanh::lean_box(0);
                                            v_isShared_6926_ = v_isSharedCheck_6930_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_6907_);
                                v___x_6931_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(
                                    v_arg_6906_,
                                    v_a_6893_,
                                    v_a_6894_,
                                    v_a_6895_,
                                    v_a_6896_,
                                );
                                if leanh::lean_obj_tag(v___x_6931_) == 0 {
                                    v_a_6932_ = leanh::lean_ctor_get(v___x_6931_, 0);
                                    v_isSharedCheck_6940_ =
                                        (!leanh::lean_is_exclusive(v___x_6931_)) as u8;
                                    if v_isSharedCheck_6940_ == 0 {
                                        v___x_6934_ = v___x_6931_;
                                        v_isShared_6935_ = v_isSharedCheck_6940_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6932_);
                                        leanh::lean_dec(v___x_6931_);
                                        v___x_6934_ = leanh::lean_box(0);
                                        v_isShared_6935_ = v_isSharedCheck_6940_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    v_a_6941_ = leanh::lean_ctor_get(v___x_6931_, 0);
                                    v_isSharedCheck_6948_ =
                                        (!leanh::lean_is_exclusive(v___x_6931_)) as u8;
                                    if v_isSharedCheck_6948_ == 0 {
                                        v___x_6943_ = v___x_6931_;
                                        v_isShared_6944_ = v_isSharedCheck_6948_;
                                        state = 8;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6941_);
                                        leanh::lean_dec(v___x_6931_);
                                        v___x_6943_ = leanh::lean_box(0);
                                        v_isShared_6944_ = v_isSharedCheck_6948_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_6892_);
                        v_a_6949_ = leanh::lean_ctor_get(v___x_6902_, 0);
                        v_isSharedCheck_6956_ =
                            (!leanh::lean_is_exclusive(v___x_6902_)) as u8;
                        if v_isSharedCheck_6956_ == 0 {
                            v___x_6951_ = v___x_6902_;
                            v_isShared_6952_ = v_isSharedCheck_6956_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6949_);
                            leanh::lean_dec(v___x_6902_);
                            v___x_6951_ = leanh::lean_box(0);
                            v_isShared_6952_ = v_isSharedCheck_6956_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_6899_);
                    leanh::lean_dec_ref(v_e_6892_);
                    return v___y_6900_;
                }
            }
            2 => {
                v___x_6918_ = lean_nat_to_int(v_a_6914_);
                if v_isShared_6917_ == 0 {
                    leanh::lean_ctor_set(v___x_6916_, 0, v___x_6918_);
                    v___x_6920_ = v___x_6916_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6921_, 0, v___x_6918_);
                    v___x_6920_ = v_reuseFailAlloc_6921_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6920_;
            }
            4 => {
                if v_isShared_6926_ == 0 {
                    v___x_6928_ = v___x_6925_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6929_, 0, v_a_6923_);
                    v___x_6928_ = v_reuseFailAlloc_6929_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6928_;
            }
            6 => {
                v___x_6936_ = lean_int_neg_succ_of_nat(v_a_6932_);
                if v_isShared_6935_ == 0 {
                    leanh::lean_ctor_set(v___x_6934_, 0, v___x_6936_);
                    v___x_6938_ = v___x_6934_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6939_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6939_, 0, v___x_6936_);
                    v___x_6938_ = v_reuseFailAlloc_6939_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6938_;
            }
            8 => {
                if v_isShared_6944_ == 0 {
                    v___x_6946_ = v___x_6943_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6947_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6947_, 0, v_a_6941_);
                    v___x_6946_ = v_reuseFailAlloc_6947_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6946_;
            }
            10 => {
                if v_isShared_6952_ == 0 {
                    v___x_6954_ = v___x_6951_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6955_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6955_, 0, v_a_6949_);
                    v___x_6954_ = v_reuseFailAlloc_6955_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6954_;
            }
            12 => {
                if v___y_6963_ == 0 {
                    leanh::lean_dec_ref_known(v___x_6960_, 1);
                    v___x_6964_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_6958_, v_a_6894_, v_a_6896_);
                    leanh::lean_dec(v_a_6958_);
                    if leanh::lean_obj_tag(v___x_6964_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6964_, 1);
                        v___x_6965_ = l_Lean_Meta_saveState___redArg(v_a_6894_, v_a_6896_);
                        if leanh::lean_obj_tag(v___x_6965_) == 0 {
                            v_a_6966_ = leanh::lean_ctor_get(v___x_6965_, 0);
                            leanh::lean_inc(v_a_6966_);
                            leanh::lean_dec_ref_known(v___x_6965_, 1);
                            leanh::lean_inc_ref(v_e_6892_);
                            v___x_6967_ =
                                l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_6892_);
                            if leanh::lean_obj_tag(v___x_6967_) == 0 {
                                leanh::lean_dec(v_a_6966_);
                                leanh::lean_dec_ref(v_e_6892_);
                                v_a_6968_ = leanh::lean_ctor_get(v___x_6967_, 0);
                                v_isSharedCheck_6976_ =
                                    (!leanh::lean_is_exclusive(v___x_6967_)) as u8;
                                if v_isSharedCheck_6976_ == 0 {
                                    v___x_6970_ = v___x_6967_;
                                    v_isShared_6971_ = v_isSharedCheck_6976_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6968_);
                                    leanh::lean_dec(v___x_6967_);
                                    v___x_6970_ = leanh::lean_box(0);
                                    v_isShared_6971_ = v_isSharedCheck_6976_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_a_6977_ = leanh::lean_ctor_get(v___x_6967_, 0);
                                v_isSharedCheck_6986_ =
                                    (!leanh::lean_is_exclusive(v___x_6967_)) as u8;
                                if v_isSharedCheck_6986_ == 0 {
                                    v___x_6979_ = v___x_6967_;
                                    v_isShared_6980_ = v_isSharedCheck_6986_;
                                    state = 15;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6977_);
                                    leanh::lean_dec(v___x_6967_);
                                    v___x_6979_ = leanh::lean_box(0);
                                    v_isShared_6980_ = v_isSharedCheck_6986_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_6892_);
                            v_a_6987_ = leanh::lean_ctor_get(v___x_6965_, 0);
                            v_isSharedCheck_6994_ =
                                (!leanh::lean_is_exclusive(v___x_6965_)) as u8;
                            if v_isSharedCheck_6994_ == 0 {
                                v___x_6989_ = v___x_6965_;
                                v_isShared_6990_ = v_isSharedCheck_6994_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6987_);
                                leanh::lean_dec(v___x_6965_);
                                v___x_6989_ = leanh::lean_box(0);
                                v_isShared_6990_ = v_isSharedCheck_6994_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_6892_);
                        v_a_6995_ = leanh::lean_ctor_get(v___x_6964_, 0);
                        v_isSharedCheck_7002_ =
                            (!leanh::lean_is_exclusive(v___x_6964_)) as u8;
                        if v_isSharedCheck_7002_ == 0 {
                            v___x_6997_ = v___x_6964_;
                            v_isShared_6998_ = v_isSharedCheck_7002_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6995_);
                            leanh::lean_dec(v___x_6964_);
                            v___x_6997_ = leanh::lean_box(0);
                            v_isShared_6998_ = v_isSharedCheck_7002_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6958_);
                    leanh::lean_dec_ref(v_e_6892_);
                    return v___x_6960_;
                }
            }
            13 => {
                v___x_6972_ = lean_nat_to_int(v_a_6968_);
                if v_isShared_6971_ == 0 {
                    leanh::lean_ctor_set(v___x_6970_, 0, v___x_6972_);
                    v___x_6974_ = v___x_6970_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6975_, 0, v___x_6972_);
                    v___x_6974_ = v_reuseFailAlloc_6975_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6974_;
            }
            15 => {
                leanh::lean_inc(v_a_6977_);
                if v_isShared_6980_ == 0 {
                    v___x_6982_ = v___x_6979_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6985_, 0, v_a_6977_);
                    v___x_6982_ = v_reuseFailAlloc_6985_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_6983_ = l_Lean_Exception_isInterrupt(v_a_6977_);
                if v___x_6983_ == 0 {
                    v___x_6984_ = l_Lean_Exception_isRuntime(v_a_6977_);
                    v___y_6899_ = v_a_6966_;
                    v___y_6900_ = v___x_6982_;
                    v___y_6901_ = v___x_6984_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6977_);
                    v___y_6899_ = v_a_6966_;
                    v___y_6900_ = v___x_6982_;
                    v___y_6901_ = v___x_6983_;
                    state = 1;
                    continue;
                }
            }
            17 => {
                if v_isShared_6990_ == 0 {
                    v___x_6992_ = v___x_6989_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6993_, 0, v_a_6987_);
                    v___x_6992_ = v_reuseFailAlloc_6993_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6992_;
            }
            19 => {
                if v_isShared_6998_ == 0 {
                    v___x_7000_ = v___x_6997_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7001_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7001_, 0, v_a_6995_);
                    v___x_7000_ = v_reuseFailAlloc_7001_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_7000_;
            }
            21 => {
                if v_isShared_7008_ == 0 {
                    v___x_7010_ = v___x_7007_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_7011_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7011_, 0, v_a_7005_);
                    v___x_7010_ = v_reuseFailAlloc_7011_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_7010_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore___boxed(
    mut v_e_7013_: *mut leanh::LeanObject,
    mut v_a_7014_: *mut leanh::LeanObject,
    mut v_a_7015_: *mut leanh::LeanObject,
    mut v_a_7016_: *mut leanh::LeanObject,
    mut v_a_7017_: *mut leanh::LeanObject,
    mut v_a_7018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7019_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(
        v_e_7013_, v_a_7014_, v_a_7015_, v_a_7016_, v_a_7017_,
    );
    leanh::lean_dec(v_a_7017_);
    leanh::lean_dec_ref(v_a_7016_);
    leanh::lean_dec(v_a_7015_);
    leanh::lean_dec_ref(v_a_7014_);
    return v_res_7019_;
}
pub unsafe fn l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(
    mut v_00_u03b1_7020_: *mut leanh::LeanObject,
    mut v_x_7021_: *mut leanh::LeanObject,
    mut v___y_7022_: *mut leanh::LeanObject,
    mut v___y_7023_: *mut leanh::LeanObject,
    mut v___y_7024_: *mut leanh::LeanObject,
    mut v___y_7025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7027_ =
        l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___redArg(
            v_x_7021_,
            v___y_7022_,
            v___y_7023_,
            v___y_7024_,
            v___y_7025_,
        );
    return v___x_7027_;
}
pub unsafe fn l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0___boxed(
    mut v_00_u03b1_7028_: *mut leanh::LeanObject,
    mut v_x_7029_: *mut leanh::LeanObject,
    mut v___y_7030_: *mut leanh::LeanObject,
    mut v___y_7031_: *mut leanh::LeanObject,
    mut v___y_7032_: *mut leanh::LeanObject,
    mut v___y_7033_: *mut leanh::LeanObject,
    mut v___y_7034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7035_ = l_Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0(
        v_00_u03b1_7028_,
        v_x_7029_,
        v___y_7030_,
        v___y_7031_,
        v___y_7032_,
        v___y_7033_,
    );
    leanh::lean_dec(v___y_7033_);
    leanh::lean_dec_ref(v___y_7032_);
    leanh::lean_dec(v___y_7031_);
    leanh::lean_dec_ref(v___y_7030_);
    return v_res_7035_;
}
pub unsafe fn l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(
    mut v_00_u03b1_7036_: *mut leanh::LeanObject,
    mut v_msg_7037_: *mut leanh::LeanObject,
    mut v___y_7038_: *mut leanh::LeanObject,
    mut v___y_7039_: *mut leanh::LeanObject,
    mut v___y_7040_: *mut leanh::LeanObject,
    mut v___y_7041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7043_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v_msg_7037_, v___y_7038_, v___y_7039_, v___y_7040_, v___y_7041_);
    return v___x_7043_;
}
pub unsafe fn l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___boxed(
    mut v_00_u03b1_7044_: *mut leanh::LeanObject,
    mut v_msg_7045_: *mut leanh::LeanObject,
    mut v___y_7046_: *mut leanh::LeanObject,
    mut v___y_7047_: *mut leanh::LeanObject,
    mut v___y_7048_: *mut leanh::LeanObject,
    mut v___y_7049_: *mut leanh::LeanObject,
    mut v___y_7050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7051_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0(v_00_u03b1_7044_, v_msg_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_);
    leanh::lean_dec(v___y_7049_);
    leanh::lean_dec_ref(v___y_7048_);
    leanh::lean_dec(v___y_7047_);
    leanh::lean_dec_ref(v___y_7046_);
    return v_res_7051_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7053_: u8 = 0;
    let mut v___x_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7053_ = 0;
    v___x_7054_ = l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__1;
    v___x_7055_ = l_Lean_MessageData_ofConstName(v___x_7054_, v___x_7053_);
    return v___x_7055_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7056_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__1,
    );
    v___x_7057_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_7058_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7058_, 0, v___x_7057_);
    leanh::lean_ctor_set(v___x_7058_, 1, v___x_7056_);
    return v___x_7058_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_7060_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__2,
    );
    v___x_7061_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7061_, 0, v___x_7060_);
    leanh::lean_ctor_set(v___x_7061_, 1, v___x_7059_);
    return v___x_7061_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(
    mut v_e_7062_: *mut leanh::LeanObject,
    mut v_a_7063_: *mut leanh::LeanObject,
    mut v_a_7064_: *mut leanh::LeanObject,
    mut v_a_7065_: *mut leanh::LeanObject,
    mut v_a_7066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7068_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__0;
    v___x_7069_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___closed__3,
    );
    v___x_7070_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___x_7068_,
        v_e_7062_,
        v___x_7069_,
        v_a_7063_,
        v_a_7064_,
        v_a_7065_,
        v_a_7066_,
    );
    return v___x_7070_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr___boxed(
    mut v_e_7071_: *mut leanh::LeanObject,
    mut v_a_7072_: *mut leanh::LeanObject,
    mut v_a_7073_: *mut leanh::LeanObject,
    mut v_a_7074_: *mut leanh::LeanObject,
    mut v_a_7075_: *mut leanh::LeanObject,
    mut v_a_7076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7077_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(
        v_e_7071_, v_a_7072_, v_a_7073_, v_a_7074_, v_a_7075_,
    );
    leanh::lean_dec(v_a_7075_);
    leanh::lean_dec_ref(v_a_7074_);
    leanh::lean_dec(v_a_7073_);
    leanh::lean_dec_ref(v_a_7072_);
    return v_res_7077_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(
    mut v_x_7078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7084_: u8 = 0;
    let mut v___x_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7088_: u8 = 0;
    let mut v___x_7089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7078_) == 9 {
                    v_a_7080_ = leanh::lean_ctor_get(v_x_7078_, 0);
                    leanh::lean_inc_ref(v_a_7080_);
                    leanh::lean_dec_ref_known(v_x_7078_, 1);
                    if leanh::lean_obj_tag(v_a_7080_) == 1 {
                        v_val_7081_ = leanh::lean_ctor_get(v_a_7080_, 0);
                        v_isSharedCheck_7088_ = (!leanh::lean_is_exclusive(v_a_7080_)) as u8;
                        if v_isSharedCheck_7088_ == 0 {
                            v___x_7083_ = v_a_7080_;
                            v_isShared_7084_ = v_isSharedCheck_7088_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_7081_);
                            leanh::lean_dec(v_a_7080_);
                            v___x_7083_ = leanh::lean_box(0);
                            v_isShared_7084_ = v_isSharedCheck_7088_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_7080_);
                        v___x_7089_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                        return v___x_7089_;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_7078_);
                    v___x_7090_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                    return v___x_7090_;
                }
            }
            1 => {
                if v_isShared_7084_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7083_, 0);
                    v___x_7086_ = v___x_7083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7087_, 0, v_val_7081_);
                    v___x_7086_ = v_reuseFailAlloc_7087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg___boxed(
    mut v_x_7091_: *mut leanh::LeanObject,
    mut v_a_7092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7093_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_7091_);
    return v_res_7093_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(
    mut v_x_7094_: *mut leanh::LeanObject,
    mut v_a_7095_: *mut leanh::LeanObject,
    mut v_a_7096_: *mut leanh::LeanObject,
    mut v_a_7097_: *mut leanh::LeanObject,
    mut v_a_7098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7100_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(v_x_7094_);
    return v___x_7100_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___boxed(
    mut v_x_7101_: *mut leanh::LeanObject,
    mut v_a_7102_: *mut leanh::LeanObject,
    mut v_a_7103_: *mut leanh::LeanObject,
    mut v_a_7104_: *mut leanh::LeanObject,
    mut v_a_7105_: *mut leanh::LeanObject,
    mut v_a_7106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7107_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore(
        v_x_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_,
    );
    leanh::lean_dec(v_a_7105_);
    leanh::lean_dec_ref(v_a_7104_);
    leanh::lean_dec(v_a_7103_);
    leanh::lean_dec_ref(v_a_7102_);
    return v_res_7107_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7109_: u8 = 0;
    let mut v___x_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7109_ = 0;
    v___x_7110_ = l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__1;
    v___x_7111_ = l_Lean_MessageData_ofConstName(v___x_7110_, v___x_7109_);
    return v___x_7111_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7112_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__1,
    );
    v___x_7113_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_7114_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7114_, 0, v___x_7113_);
    leanh::lean_ctor_set(v___x_7114_, 1, v___x_7112_);
    return v___x_7114_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7115_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_7116_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__2,
    );
    v___x_7117_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7117_, 0, v___x_7116_);
    leanh::lean_ctor_set(v___x_7117_, 1, v___x_7115_);
    return v___x_7117_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(
    mut v_e_7118_: *mut leanh::LeanObject,
    mut v_a_7119_: *mut leanh::LeanObject,
    mut v_a_7120_: *mut leanh::LeanObject,
    mut v_a_7121_: *mut leanh::LeanObject,
    mut v_a_7122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7124_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__0;
    v___x_7125_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___closed__3,
    );
    v___x_7126_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___x_7124_,
        v_e_7118_,
        v___x_7125_,
        v_a_7119_,
        v_a_7120_,
        v_a_7121_,
        v_a_7122_,
    );
    return v___x_7126_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr___boxed(
    mut v_e_7127_: *mut leanh::LeanObject,
    mut v_a_7128_: *mut leanh::LeanObject,
    mut v_a_7129_: *mut leanh::LeanObject,
    mut v_a_7130_: *mut leanh::LeanObject,
    mut v_a_7131_: *mut leanh::LeanObject,
    mut v_a_7132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7133_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(
        v_e_7127_, v_a_7128_, v_a_7129_, v_a_7130_, v_a_7131_,
    );
    leanh::lean_dec(v_a_7131_);
    leanh::lean_dec_ref(v_a_7130_);
    leanh::lean_dec(v_a_7129_);
    leanh::lean_dec_ref(v_a_7128_);
    return v_res_7133_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(
    mut v_e_7134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7141_: u8 = 0;
    let mut v___x_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7136_ = l_Lean_Expr_name_x3f(v_e_7134_);
                if leanh::lean_obj_tag(v___x_7136_) == 0 {
                    v___x_7137_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                    return v___x_7137_;
                } else {
                    v_val_7138_ = leanh::lean_ctor_get(v___x_7136_, 0);
                    v_isSharedCheck_7145_ = (!leanh::lean_is_exclusive(v___x_7136_)) as u8;
                    if v_isSharedCheck_7145_ == 0 {
                        v___x_7140_ = v___x_7136_;
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7138_);
                        leanh::lean_dec(v___x_7136_);
                        v___x_7140_ = leanh::lean_box(0);
                        v_isShared_7141_ = v_isSharedCheck_7145_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7141_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7140_, 0);
                    v___x_7143_ = v___x_7140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7144_, 0, v_val_7138_);
                    v___x_7143_ = v_reuseFailAlloc_7144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg___boxed(
    mut v_e_7146_: *mut leanh::LeanObject,
    mut v_a_7147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7148_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_7146_);
    return v_res_7148_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(
    mut v_e_7149_: *mut leanh::LeanObject,
    mut v_a_7150_: *mut leanh::LeanObject,
    mut v_a_7151_: *mut leanh::LeanObject,
    mut v_a_7152_: *mut leanh::LeanObject,
    mut v_a_7153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7155_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(v_e_7149_);
    return v___x_7155_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___boxed(
    mut v_e_7156_: *mut leanh::LeanObject,
    mut v_a_7157_: *mut leanh::LeanObject,
    mut v_a_7158_: *mut leanh::LeanObject,
    mut v_a_7159_: *mut leanh::LeanObject,
    mut v_a_7160_: *mut leanh::LeanObject,
    mut v_a_7161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7162_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore(
        v_e_7156_, v_a_7157_, v_a_7158_, v_a_7159_, v_a_7160_,
    );
    leanh::lean_dec(v_a_7160_);
    leanh::lean_dec_ref(v_a_7159_);
    leanh::lean_dec(v_a_7158_);
    leanh::lean_dec_ref(v_a_7157_);
    return v_res_7162_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7164_: u8 = 0;
    let mut v___x_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7164_ = 0;
    v___x_7165_ = l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__1;
    v___x_7166_ = l_Lean_MessageData_ofConstName(v___x_7165_, v___x_7164_);
    return v___x_7166_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7167_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__1,
    );
    v___x_7168_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_7169_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7169_, 0, v___x_7168_);
    leanh::lean_ctor_set(v___x_7169_, 1, v___x_7167_);
    return v___x_7169_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7170_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_7171_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__2,
    );
    v___x_7172_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7172_, 0, v___x_7171_);
    leanh::lean_ctor_set(v___x_7172_, 1, v___x_7170_);
    return v___x_7172_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(
    mut v_e_7173_: *mut leanh::LeanObject,
    mut v_a_7174_: *mut leanh::LeanObject,
    mut v_a_7175_: *mut leanh::LeanObject,
    mut v_a_7176_: *mut leanh::LeanObject,
    mut v_a_7177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7179_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__0;
    v___x_7180_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___closed__3,
    );
    v___x_7181_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___x_7179_,
        v_e_7173_,
        v___x_7180_,
        v_a_7174_,
        v_a_7175_,
        v_a_7176_,
        v_a_7177_,
    );
    return v___x_7181_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr___boxed(
    mut v_e_7182_: *mut leanh::LeanObject,
    mut v_a_7183_: *mut leanh::LeanObject,
    mut v_a_7184_: *mut leanh::LeanObject,
    mut v_a_7185_: *mut leanh::LeanObject,
    mut v_a_7186_: *mut leanh::LeanObject,
    mut v_a_7187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7188_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(
        v_e_7182_, v_a_7183_, v_a_7184_, v_a_7185_, v_a_7186_,
    );
    leanh::lean_dec(v_a_7186_);
    leanh::lean_dec_ref(v_a_7185_);
    leanh::lean_dec(v_a_7184_);
    leanh::lean_dec_ref(v_a_7183_);
    return v_res_7188_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(
    mut v_ev_7192_: *mut leanh::LeanObject,
    mut v_e_7193_: *mut leanh::LeanObject,
    mut v_a_7194_: *mut leanh::LeanObject,
    mut v_a_7195_: *mut leanh::LeanObject,
    mut v_a_7196_: *mut leanh::LeanObject,
    mut v_a_7197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: u8 = 0;
    let mut v___x_7201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: u8 = 0;
    let mut v___x_7206_: u8 = 0;
    let mut v___x_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7210_: u8 = 0;
    let mut v___x_7211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7216_: u8 = 0;
    let mut v___x_7217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7221_: u8 = 0;
    let mut v_a_7222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7225_: u8 = 0;
    let mut v___x_7227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7229_: u8 = 0;
    let mut v___x_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7199_ = l_Lean_Expr_cleanupAnnotations(v_e_7193_);
                v___x_7200_ = l_Lean_Expr_isApp(v___x_7199_);
                if v___x_7200_ == 0 {
                    leanh::lean_dec_ref(v___x_7199_);
                    leanh::lean_dec_ref(v_ev_7192_);
                    v___x_7201_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                    return v___x_7201_;
                } else {
                    v_arg_7202_ = leanh::lean_ctor_get(v___x_7199_, 1);
                    leanh::lean_inc_ref(v_arg_7202_);
                    v___x_7203_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7199_);
                    v___x_7204_ =
                        l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__8;
                    v___x_7205_ = l_Lean_Expr_isConstOf(v___x_7203_, v___x_7204_);
                    if v___x_7205_ == 0 {
                        v___x_7206_ = l_Lean_Expr_isApp(v___x_7203_);
                        if v___x_7206_ == 0 {
                            leanh::lean_dec_ref(v___x_7203_);
                            leanh::lean_dec_ref(v_arg_7202_);
                            leanh::lean_dec_ref(v_ev_7192_);
                            v___x_7207_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                            return v___x_7207_;
                        } else {
                            v___x_7208_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7203_);
                            v___x_7209_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___closed__0;
                            v___x_7210_ = l_Lean_Expr_isConstOf(v___x_7208_, v___x_7209_);
                            leanh::lean_dec_ref(v___x_7208_);
                            if v___x_7210_ == 0 {
                                leanh::lean_dec_ref(v_arg_7202_);
                                leanh::lean_dec_ref(v_ev_7192_);
                                v___x_7211_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                                return v___x_7211_;
                            } else {
                                leanh::lean_inc(v_a_7197_);
                                leanh::lean_inc_ref(v_a_7196_);
                                leanh::lean_inc(v_a_7195_);
                                leanh::lean_inc_ref(v_a_7194_);
                                v___x_7212_ = leanh::lean_apply_6(
                                    v_ev_7192_,
                                    v_arg_7202_,
                                    v_a_7194_,
                                    v_a_7195_,
                                    v_a_7196_,
                                    v_a_7197_,
                                    leanh::lean_box(0),
                                );
                                if leanh::lean_obj_tag(v___x_7212_) == 0 {
                                    v_a_7213_ = leanh::lean_ctor_get(v___x_7212_, 0);
                                    v_isSharedCheck_7221_ =
                                        (!leanh::lean_is_exclusive(v___x_7212_)) as u8;
                                    if v_isSharedCheck_7221_ == 0 {
                                        v___x_7215_ = v___x_7212_;
                                        v_isShared_7216_ = v_isSharedCheck_7221_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7213_);
                                        leanh::lean_dec(v___x_7212_);
                                        v___x_7215_ = leanh::lean_box(0);
                                        v_isShared_7216_ = v_isSharedCheck_7221_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_7222_ = leanh::lean_ctor_get(v___x_7212_, 0);
                                    v_isSharedCheck_7229_ =
                                        (!leanh::lean_is_exclusive(v___x_7212_)) as u8;
                                    if v_isSharedCheck_7229_ == 0 {
                                        v___x_7224_ = v___x_7212_;
                                        v_isShared_7225_ = v_isSharedCheck_7229_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7222_);
                                        leanh::lean_dec(v___x_7212_);
                                        v___x_7224_ = leanh::lean_box(0);
                                        v_isShared_7225_ = v_isSharedCheck_7229_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_7203_);
                        leanh::lean_dec_ref(v_arg_7202_);
                        leanh::lean_dec_ref(v_ev_7192_);
                        v___x_7230_ = leanh::lean_box(0);
                        v___x_7231_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7231_, 0, v___x_7230_);
                        return v___x_7231_;
                    }
                }
            }
            1 => {
                v___x_7217_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7217_, 0, v_a_7213_);
                if v_isShared_7216_ == 0 {
                    leanh::lean_ctor_set(v___x_7215_, 0, v___x_7217_);
                    v___x_7219_ = v___x_7215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7220_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7220_, 0, v___x_7217_);
                    v___x_7219_ = v_reuseFailAlloc_7220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7219_;
            }
            3 => {
                if v_isShared_7225_ == 0 {
                    v___x_7227_ = v___x_7224_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7228_, 0, v_a_7222_);
                    v___x_7227_ = v_reuseFailAlloc_7228_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg___boxed(
    mut v_ev_7232_: *mut leanh::LeanObject,
    mut v_e_7233_: *mut leanh::LeanObject,
    mut v_a_7234_: *mut leanh::LeanObject,
    mut v_a_7235_: *mut leanh::LeanObject,
    mut v_a_7236_: *mut leanh::LeanObject,
    mut v_a_7237_: *mut leanh::LeanObject,
    mut v_a_7238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7239_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(
        v_ev_7232_, v_e_7233_, v_a_7234_, v_a_7235_, v_a_7236_, v_a_7237_,
    );
    leanh::lean_dec(v_a_7237_);
    leanh::lean_dec_ref(v_a_7236_);
    leanh::lean_dec(v_a_7235_);
    leanh::lean_dec_ref(v_a_7234_);
    return v_res_7239_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(
    mut v_00_u03b1_7240_: *mut leanh::LeanObject,
    mut v_ev_7241_: *mut leanh::LeanObject,
    mut v_e_7242_: *mut leanh::LeanObject,
    mut v_a_7243_: *mut leanh::LeanObject,
    mut v_a_7244_: *mut leanh::LeanObject,
    mut v_a_7245_: *mut leanh::LeanObject,
    mut v_a_7246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7248_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___redArg(
        v_ev_7241_, v_e_7242_, v_a_7243_, v_a_7244_, v_a_7245_, v_a_7246_,
    );
    return v___x_7248_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed(
    mut v_00_u03b1_7249_: *mut leanh::LeanObject,
    mut v_ev_7250_: *mut leanh::LeanObject,
    mut v_e_7251_: *mut leanh::LeanObject,
    mut v_a_7252_: *mut leanh::LeanObject,
    mut v_a_7253_: *mut leanh::LeanObject,
    mut v_a_7254_: *mut leanh::LeanObject,
    mut v_a_7255_: *mut leanh::LeanObject,
    mut v_a_7256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7257_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore(
        v_00_u03b1_7249_,
        v_ev_7250_,
        v_e_7251_,
        v_a_7252_,
        v_a_7253_,
        v_a_7254_,
        v_a_7255_,
    );
    leanh::lean_dec(v_a_7255_);
    leanh::lean_dec_ref(v_a_7254_);
    leanh::lean_dec(v_a_7253_);
    leanh::lean_dec_ref(v_a_7252_);
    return v_res_7257_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7258_: u8 = 0;
    let mut v___x_7259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7258_ = 0;
    v___x_7259_ = l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__1;
    v___x_7260_ = l_Lean_MessageData_ofConstName(v___x_7259_, v___x_7258_);
    return v___x_7260_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7261_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__0,
    );
    v___x_7262_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_7263_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7263_, 0, v___x_7262_);
    leanh::lean_ctor_set(v___x_7263_, 1, v___x_7261_);
    return v___x_7263_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7264_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_7265_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__1,
    );
    v___x_7266_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7266_, 0, v___x_7265_);
    leanh::lean_ctor_set(v___x_7266_, 1, v___x_7264_);
    return v___x_7266_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(
    mut v_ev_7267_: *mut leanh::LeanObject,
    mut v_e_7268_: *mut leanh::LeanObject,
    mut v_a_7269_: *mut leanh::LeanObject,
    mut v_a_7270_: *mut leanh::LeanObject,
    mut v_a_7271_: *mut leanh::LeanObject,
    mut v_a_7272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7281_: u8 = 0;
    let mut v___x_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7284_: u8 = 0;
    let mut v___x_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7290_: u8 = 0;
    let mut v___x_7292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7297_: u8 = 0;
    let mut v_a_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7301_: u8 = 0;
    let mut v___x_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7305_: u8 = 0;
    let mut v_a_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7309_: u8 = 0;
    let mut v___x_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7313_: u8 = 0;
    let mut v_isSharedCheck_7314_: u8 = 0;
    let mut v_unused_7315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: u8 = 0;
    let mut v___x_7317_: u8 = 0;
    let mut v_a_7318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7321_: u8 = 0;
    let mut v___x_7323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7274_ = l_Lean_Meta_saveState___redArg(v_a_7270_, v_a_7272_);
                if leanh::lean_obj_tag(v___x_7274_) == 0 {
                    v_a_7275_ = leanh::lean_ctor_get(v___x_7274_, 0);
                    leanh::lean_inc(v_a_7275_);
                    leanh::lean_dec_ref_known(v___x_7274_, 1);
                    leanh::lean_inc_ref(v_ev_7267_);
                    v___x_7276_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExprCore___boxed
                            as *mut core::ffi::c_void,
                        8,
                        2,
                    );
                    leanh::lean_closure_set(v___x_7276_, 0, leanh::lean_box(0));
                    leanh::lean_closure_set(v___x_7276_, 1, v_ev_7267_);
                    v___x_7277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2_once), _init_l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___closed__2);
                    leanh::lean_inc_ref(v_e_7268_);
                    v___x_7278_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
                        v___x_7276_,
                        v_e_7268_,
                        v___x_7277_,
                        v_a_7269_,
                        v_a_7270_,
                        v_a_7271_,
                        v_a_7272_,
                    );
                    if leanh::lean_obj_tag(v___x_7278_) == 0 {
                        leanh::lean_dec(v_a_7275_);
                        leanh::lean_dec_ref(v_e_7268_);
                        leanh::lean_dec_ref(v_ev_7267_);
                        return v___x_7278_;
                    } else {
                        v_a_7279_ = leanh::lean_ctor_get(v___x_7278_, 0);
                        leanh::lean_inc(v_a_7279_);
                        v___x_7316_ = l_Lean_Exception_isInterrupt(v_a_7279_);
                        if v___x_7316_ == 0 {
                            v___x_7317_ = l_Lean_Exception_isRuntime(v_a_7279_);
                            v___y_7281_ = v___x_7317_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_7279_);
                            v___y_7281_ = v___x_7316_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7268_);
                    leanh::lean_dec_ref(v_ev_7267_);
                    v_a_7318_ = leanh::lean_ctor_get(v___x_7274_, 0);
                    v_isSharedCheck_7325_ = (!leanh::lean_is_exclusive(v___x_7274_)) as u8;
                    if v_isSharedCheck_7325_ == 0 {
                        v___x_7320_ = v___x_7274_;
                        v_isShared_7321_ = v_isSharedCheck_7325_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7318_);
                        leanh::lean_dec(v___x_7274_);
                        v___x_7320_ = leanh::lean_box(0);
                        v_isShared_7321_ = v_isSharedCheck_7325_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_7281_ == 0 {
                    v_isSharedCheck_7314_ = (!leanh::lean_is_exclusive(v___x_7278_)) as u8;
                    if v_isSharedCheck_7314_ == 0 {
                        v_unused_7315_ = leanh::lean_ctor_get(v___x_7278_, 0);
                        leanh::lean_dec(v_unused_7315_);
                        v___x_7283_ = v___x_7278_;
                        v_isShared_7284_ = v_isSharedCheck_7314_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7278_);
                        v___x_7283_ = leanh::lean_box(0);
                        v_isShared_7284_ = v_isSharedCheck_7314_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7275_);
                    leanh::lean_dec_ref(v_e_7268_);
                    leanh::lean_dec_ref(v_ev_7267_);
                    return v___x_7278_;
                }
            }
            2 => {
                v___x_7285_ =
                    l_Lean_Meta_SavedState_restore___redArg(v_a_7275_, v_a_7270_, v_a_7272_);
                leanh::lean_dec(v_a_7275_);
                if leanh::lean_obj_tag(v___x_7285_) == 0 {
                    leanh::lean_dec_ref_known(v___x_7285_, 1);
                    leanh::lean_inc(v_a_7272_);
                    leanh::lean_inc_ref(v_a_7271_);
                    leanh::lean_inc(v_a_7270_);
                    leanh::lean_inc_ref(v_a_7269_);
                    v___x_7286_ = leanh::lean_apply_6(
                        v_ev_7267_,
                        v_e_7268_,
                        v_a_7269_,
                        v_a_7270_,
                        v_a_7271_,
                        v_a_7272_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_7286_) == 0 {
                        v_a_7287_ = leanh::lean_ctor_get(v___x_7286_, 0);
                        v_isSharedCheck_7297_ =
                            (!leanh::lean_is_exclusive(v___x_7286_)) as u8;
                        if v_isSharedCheck_7297_ == 0 {
                            v___x_7289_ = v___x_7286_;
                            v_isShared_7290_ = v_isSharedCheck_7297_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7287_);
                            leanh::lean_dec(v___x_7286_);
                            v___x_7289_ = leanh::lean_box(0);
                            v_isShared_7290_ = v_isSharedCheck_7297_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_7283_);
                        v_a_7298_ = leanh::lean_ctor_get(v___x_7286_, 0);
                        v_isSharedCheck_7305_ =
                            (!leanh::lean_is_exclusive(v___x_7286_)) as u8;
                        if v_isSharedCheck_7305_ == 0 {
                            v___x_7300_ = v___x_7286_;
                            v_isShared_7301_ = v_isSharedCheck_7305_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7298_);
                            leanh::lean_dec(v___x_7286_);
                            v___x_7300_ = leanh::lean_box(0);
                            v_isShared_7301_ = v_isSharedCheck_7305_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7283_);
                    leanh::lean_dec_ref(v_e_7268_);
                    leanh::lean_dec_ref(v_ev_7267_);
                    v_a_7306_ = leanh::lean_ctor_get(v___x_7285_, 0);
                    v_isSharedCheck_7313_ = (!leanh::lean_is_exclusive(v___x_7285_)) as u8;
                    if v_isSharedCheck_7313_ == 0 {
                        v___x_7308_ = v___x_7285_;
                        v_isShared_7309_ = v_isSharedCheck_7313_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7306_);
                        leanh::lean_dec(v___x_7285_);
                        v___x_7308_ = leanh::lean_box(0);
                        v_isShared_7309_ = v_isSharedCheck_7313_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7284_ == 0 {
                    leanh::lean_ctor_set(v___x_7283_, 0, v_a_7287_);
                    v___x_7292_ = v___x_7283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7296_, 0, v_a_7287_);
                    v___x_7292_ = v_reuseFailAlloc_7296_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7290_ == 0 {
                    leanh::lean_ctor_set(v___x_7289_, 0, v___x_7292_);
                    v___x_7294_ = v___x_7289_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7295_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7295_, 0, v___x_7292_);
                    v___x_7294_ = v_reuseFailAlloc_7295_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7294_;
            }
            6 => {
                if v_isShared_7301_ == 0 {
                    v___x_7303_ = v___x_7300_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7304_, 0, v_a_7298_);
                    v___x_7303_ = v_reuseFailAlloc_7304_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7303_;
            }
            8 => {
                if v_isShared_7309_ == 0 {
                    v___x_7311_ = v___x_7308_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7312_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7312_, 0, v_a_7306_);
                    v___x_7311_ = v_reuseFailAlloc_7312_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7311_;
            }
            10 => {
                if v_isShared_7321_ == 0 {
                    v___x_7323_ = v___x_7320_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7324_, 0, v_a_7318_);
                    v___x_7323_ = v_reuseFailAlloc_7324_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg___boxed(
    mut v_ev_7326_: *mut leanh::LeanObject,
    mut v_e_7327_: *mut leanh::LeanObject,
    mut v_a_7328_: *mut leanh::LeanObject,
    mut v_a_7329_: *mut leanh::LeanObject,
    mut v_a_7330_: *mut leanh::LeanObject,
    mut v_a_7331_: *mut leanh::LeanObject,
    mut v_a_7332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7333_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(
        v_ev_7326_, v_e_7327_, v_a_7328_, v_a_7329_, v_a_7330_, v_a_7331_,
    );
    leanh::lean_dec(v_a_7331_);
    leanh::lean_dec_ref(v_a_7330_);
    leanh::lean_dec(v_a_7329_);
    leanh::lean_dec_ref(v_a_7328_);
    return v_res_7333_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(
    mut v_00_u03b1_7334_: *mut leanh::LeanObject,
    mut v_ev_7335_: *mut leanh::LeanObject,
    mut v_e_7336_: *mut leanh::LeanObject,
    mut v_a_7337_: *mut leanh::LeanObject,
    mut v_a_7338_: *mut leanh::LeanObject,
    mut v_a_7339_: *mut leanh::LeanObject,
    mut v_a_7340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7342_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___redArg(
        v_ev_7335_, v_e_7336_, v_a_7337_, v_a_7338_, v_a_7339_, v_a_7340_,
    );
    return v___x_7342_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed(
    mut v_00_u03b1_7343_: *mut leanh::LeanObject,
    mut v_ev_7344_: *mut leanh::LeanObject,
    mut v_e_7345_: *mut leanh::LeanObject,
    mut v_a_7346_: *mut leanh::LeanObject,
    mut v_a_7347_: *mut leanh::LeanObject,
    mut v_a_7348_: *mut leanh::LeanObject,
    mut v_a_7349_: *mut leanh::LeanObject,
    mut v_a_7350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7351_ = l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr(
        v_00_u03b1_7343_,
        v_ev_7344_,
        v_e_7345_,
        v_a_7346_,
        v_a_7347_,
        v_a_7348_,
        v_a_7349_,
    );
    leanh::lean_dec(v_a_7349_);
    leanh::lean_dec_ref(v_a_7348_);
    leanh::lean_dec(v_a_7347_);
    leanh::lean_dec_ref(v_a_7346_);
    return v_res_7351_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7353_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__0;
    v___x_7354_ = l_Lean_stringToMessageData(v___x_7353_);
    return v___x_7354_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7355_: u8 = 0;
    let mut v___x_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7355_ = 0;
    v___x_7356_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__0;
    v___x_7357_ = l_Lean_MessageData_ofConstName(v___x_7356_, v___x_7355_);
    return v___x_7357_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(
    mut v_ev_7358_: *mut leanh::LeanObject,
    mut v_e_7359_: *mut leanh::LeanObject,
    mut v_didWHNF_7360_: u8,
    mut v_a_7361_: *mut leanh::LeanObject,
    mut v_a_7362_: *mut leanh::LeanObject,
    mut v_a_7363_: *mut leanh::LeanObject,
    mut v_a_7364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7373_: u8 = 0;
    let mut v_a_7375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7378_: u8 = 0;
    let mut v___x_7380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7382_: u8 = 0;
    let mut v___x_7383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: u8 = 0;
    let mut v_arg_7395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: u8 = 0;
    let mut v___x_7399_: u8 = 0;
    let mut v_arg_7400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: u8 = 0;
    let mut v___x_7403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: u8 = 0;
    let mut v___x_7406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7412_: u8 = 0;
    let mut v___x_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7417_: u8 = 0;
    let mut v_a_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7421_: u8 = 0;
    let mut v___x_7423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7425_: u8 = 0;
    let mut v___x_7426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_7359_);
                v___x_7393_ = l_Lean_Expr_cleanupAnnotations(v_e_7359_);
                v___x_7394_ = l_Lean_Expr_isApp(v___x_7393_);
                if v___x_7394_ == 0 {
                    leanh::lean_dec_ref(v___x_7393_);
                    v___y_7367_ = v_a_7361_;
                    v___y_7368_ = v_a_7362_;
                    v___y_7369_ = v_a_7363_;
                    v___y_7370_ = v_a_7364_;
                    state = 1;
                    continue;
                } else {
                    v_arg_7395_ = leanh::lean_ctor_get(v___x_7393_, 1);
                    leanh::lean_inc_ref(v_arg_7395_);
                    v___x_7396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7393_);
                    v___x_7397_ = l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__5;
                    v___x_7398_ = l_Lean_Expr_isConstOf(v___x_7396_, v___x_7397_);
                    if v___x_7398_ == 0 {
                        v___x_7399_ = l_Lean_Expr_isApp(v___x_7396_);
                        if v___x_7399_ == 0 {
                            leanh::lean_dec_ref(v___x_7396_);
                            leanh::lean_dec_ref(v_arg_7395_);
                            v___y_7367_ = v_a_7361_;
                            v___y_7368_ = v_a_7362_;
                            v___y_7369_ = v_a_7363_;
                            v___y_7370_ = v_a_7364_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_7400_ = leanh::lean_ctor_get(v___x_7396_, 1);
                            leanh::lean_inc_ref(v_arg_7400_);
                            v___x_7401_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7396_);
                            v___x_7402_ = l_Lean_Expr_isApp(v___x_7401_);
                            if v___x_7402_ == 0 {
                                leanh::lean_dec_ref(v___x_7401_);
                                leanh::lean_dec_ref(v_arg_7400_);
                                leanh::lean_dec_ref(v_arg_7395_);
                                v___y_7367_ = v_a_7361_;
                                v___y_7368_ = v_a_7362_;
                                v___y_7369_ = v_a_7363_;
                                v___y_7370_ = v_a_7364_;
                                state = 1;
                                continue;
                            } else {
                                v___x_7403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7401_);
                                v___x_7404_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Elab_ConfigEval_EvalTerm_evalListStx_spec__2___closed__2;
                                v___x_7405_ = l_Lean_Expr_isConstOf(v___x_7403_, v___x_7404_);
                                leanh::lean_dec_ref(v___x_7403_);
                                if v___x_7405_ == 0 {
                                    leanh::lean_dec_ref(v_arg_7400_);
                                    leanh::lean_dec_ref(v_arg_7395_);
                                    v___y_7367_ = v_a_7361_;
                                    v___y_7368_ = v_a_7362_;
                                    v___y_7369_ = v_a_7363_;
                                    v___y_7370_ = v_a_7364_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_e_7359_);
                                    leanh::lean_inc_ref(v_ev_7358_);
                                    leanh::lean_inc(v_a_7364_);
                                    leanh::lean_inc_ref(v_a_7363_);
                                    leanh::lean_inc(v_a_7362_);
                                    leanh::lean_inc_ref(v_a_7361_);
                                    v___x_7406_ = leanh::lean_apply_6(
                                        v_ev_7358_,
                                        v_arg_7400_,
                                        v_a_7361_,
                                        v_a_7362_,
                                        v_a_7363_,
                                        v_a_7364_,
                                        leanh::lean_box(0),
                                    );
                                    if leanh::lean_obj_tag(v___x_7406_) == 0 {
                                        v_a_7407_ = leanh::lean_ctor_get(v___x_7406_, 0);
                                        leanh::lean_inc(v_a_7407_);
                                        leanh::lean_dec_ref_known(v___x_7406_, 1);
                                        v___x_7408_ =
                                            l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(
                                                v_ev_7358_,
                                                v_arg_7395_,
                                                v___x_7398_,
                                                v_a_7361_,
                                                v_a_7362_,
                                                v_a_7363_,
                                                v_a_7364_,
                                            );
                                        if leanh::lean_obj_tag(v___x_7408_) == 0 {
                                            v_a_7409_ = leanh::lean_ctor_get(v___x_7408_, 0);
                                            v_isSharedCheck_7417_ =
                                                (!leanh::lean_is_exclusive(v___x_7408_))
                                                    as u8;
                                            if v_isSharedCheck_7417_ == 0 {
                                                v___x_7411_ = v___x_7408_;
                                                v_isShared_7412_ = v_isSharedCheck_7417_;
                                                state = 4;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_7409_);
                                                leanh::lean_dec(v___x_7408_);
                                                v___x_7411_ = leanh::lean_box(0);
                                                v_isShared_7412_ = v_isSharedCheck_7417_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_7407_);
                                            return v___x_7408_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_arg_7395_);
                                        leanh::lean_dec_ref(v_ev_7358_);
                                        v_a_7418_ = leanh::lean_ctor_get(v___x_7406_, 0);
                                        v_isSharedCheck_7425_ =
                                            (!leanh::lean_is_exclusive(v___x_7406_)) as u8;
                                        if v_isSharedCheck_7425_ == 0 {
                                            v___x_7420_ = v___x_7406_;
                                            v_isShared_7421_ = v_isSharedCheck_7425_;
                                            state = 6;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_7418_);
                                            leanh::lean_dec(v___x_7406_);
                                            v___x_7420_ = leanh::lean_box(0);
                                            v_isShared_7421_ = v_isSharedCheck_7425_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_7396_);
                        leanh::lean_dec_ref(v_arg_7395_);
                        leanh::lean_dec_ref(v_e_7359_);
                        leanh::lean_dec_ref(v_ev_7358_);
                        v___x_7426_ = leanh::lean_box(0);
                        v___x_7427_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7427_, 0, v___x_7426_);
                        return v___x_7427_;
                    }
                }
            }
            1 => {
                if v_didWHNF_7360_ == 0 {
                    leanh::lean_inc(v___y_7370_);
                    leanh::lean_inc_ref(v___y_7369_);
                    leanh::lean_inc(v___y_7368_);
                    leanh::lean_inc_ref(v___y_7367_);
                    v___x_7371_ = lean_whnf(
                        v_e_7359_,
                        v___y_7367_,
                        v___y_7368_,
                        v___y_7369_,
                        v___y_7370_,
                    );
                    if leanh::lean_obj_tag(v___x_7371_) == 0 {
                        v_a_7372_ = leanh::lean_ctor_get(v___x_7371_, 0);
                        leanh::lean_inc(v_a_7372_);
                        leanh::lean_dec_ref_known(v___x_7371_, 1);
                        v___x_7373_ = 1;
                        v_e_7359_ = v_a_7372_;
                        v_didWHNF_7360_ = v___x_7373_;
                        v_a_7361_ = v___y_7367_;
                        v_a_7362_ = v___y_7368_;
                        v_a_7363_ = v___y_7369_;
                        v_a_7364_ = v___y_7370_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_ev_7358_);
                        v_a_7375_ = leanh::lean_ctor_get(v___x_7371_, 0);
                        v_isSharedCheck_7382_ =
                            (!leanh::lean_is_exclusive(v___x_7371_)) as u8;
                        if v_isSharedCheck_7382_ == 0 {
                            v___x_7377_ = v___x_7371_;
                            v_isShared_7378_ = v_isSharedCheck_7382_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7375_);
                            leanh::lean_dec(v___x_7371_);
                            v___x_7377_ = leanh::lean_box(0);
                            v_isShared_7378_ = v_isSharedCheck_7382_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_ev_7358_);
                    v___x_7383_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__1,
                    );
                    v___x_7384_ = l_Lean_indentExpr(v_e_7359_);
                    v___x_7385_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7385_, 0, v___x_7383_);
                    leanh::lean_ctor_set(v___x_7385_, 1, v___x_7384_);
                    v___x_7386_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
                    );
                    v___x_7387_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7387_, 0, v___x_7385_);
                    leanh::lean_ctor_set(v___x_7387_, 1, v___x_7386_);
                    v___x_7388_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___closed__2,
                    );
                    v___x_7389_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7389_, 0, v___x_7387_);
                    leanh::lean_ctor_set(v___x_7389_, 1, v___x_7388_);
                    v___x_7390_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once
                        ),
                        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
                    );
                    v___x_7391_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7391_, 0, v___x_7389_);
                    leanh::lean_ctor_set(v___x_7391_, 1, v___x_7390_);
                    v___x_7392_ = l_Lean_throwError___at___00Option_getM___at___00Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore_spec__0_spec__0___redArg(v___x_7391_, v___y_7367_, v___y_7368_, v___y_7369_, v___y_7370_);
                    return v___x_7392_;
                }
            }
            2 => {
                if v_isShared_7378_ == 0 {
                    v___x_7380_ = v___x_7377_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7381_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7381_, 0, v_a_7375_);
                    v___x_7380_ = v_reuseFailAlloc_7381_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7380_;
            }
            4 => {
                v___x_7413_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7413_, 0, v_a_7407_);
                leanh::lean_ctor_set(v___x_7413_, 1, v_a_7409_);
                if v_isShared_7412_ == 0 {
                    leanh::lean_ctor_set(v___x_7411_, 0, v___x_7413_);
                    v___x_7415_ = v___x_7411_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7416_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7416_, 0, v___x_7413_);
                    v___x_7415_ = v_reuseFailAlloc_7416_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7415_;
            }
            6 => {
                if v_isShared_7421_ == 0 {
                    v___x_7423_ = v___x_7420_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7424_, 0, v_a_7418_);
                    v___x_7423_ = v_reuseFailAlloc_7424_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg___boxed(
    mut v_ev_7428_: *mut leanh::LeanObject,
    mut v_e_7429_: *mut leanh::LeanObject,
    mut v_didWHNF_7430_: *mut leanh::LeanObject,
    mut v_a_7431_: *mut leanh::LeanObject,
    mut v_a_7432_: *mut leanh::LeanObject,
    mut v_a_7433_: *mut leanh::LeanObject,
    mut v_a_7434_: *mut leanh::LeanObject,
    mut v_a_7435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_didWHNF_boxed_7436_: u8 = 0;
    let mut v_res_7437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_didWHNF_boxed_7436_ = (leanh::lean_unbox(v_didWHNF_7430_) as u8);
    v_res_7437_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(
        v_ev_7428_,
        v_e_7429_,
        v_didWHNF_boxed_7436_,
        v_a_7431_,
        v_a_7432_,
        v_a_7433_,
        v_a_7434_,
    );
    leanh::lean_dec(v_a_7434_);
    leanh::lean_dec_ref(v_a_7433_);
    leanh::lean_dec(v_a_7432_);
    leanh::lean_dec_ref(v_a_7431_);
    return v_res_7437_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(
    mut v_00_u03b1_7438_: *mut leanh::LeanObject,
    mut v_ev_7439_: *mut leanh::LeanObject,
    mut v_e_7440_: *mut leanh::LeanObject,
    mut v_didWHNF_7441_: u8,
    mut v_a_7442_: *mut leanh::LeanObject,
    mut v_a_7443_: *mut leanh::LeanObject,
    mut v_a_7444_: *mut leanh::LeanObject,
    mut v_a_7445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7447_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(
        v_ev_7439_,
        v_e_7440_,
        v_didWHNF_7441_,
        v_a_7442_,
        v_a_7443_,
        v_a_7444_,
        v_a_7445_,
    );
    return v___x_7447_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___boxed(
    mut v_00_u03b1_7448_: *mut leanh::LeanObject,
    mut v_ev_7449_: *mut leanh::LeanObject,
    mut v_e_7450_: *mut leanh::LeanObject,
    mut v_didWHNF_7451_: *mut leanh::LeanObject,
    mut v_a_7452_: *mut leanh::LeanObject,
    mut v_a_7453_: *mut leanh::LeanObject,
    mut v_a_7454_: *mut leanh::LeanObject,
    mut v_a_7455_: *mut leanh::LeanObject,
    mut v_a_7456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_didWHNF_boxed_7457_: u8 = 0;
    let mut v_res_7458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_didWHNF_boxed_7457_ = (leanh::lean_unbox(v_didWHNF_7451_) as u8);
    v_res_7458_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr(
        v_00_u03b1_7448_,
        v_ev_7449_,
        v_e_7450_,
        v_didWHNF_boxed_7457_,
        v_a_7452_,
        v_a_7453_,
        v_a_7454_,
        v_a_7455_,
    );
    leanh::lean_dec(v_a_7455_);
    leanh::lean_dec_ref(v_a_7454_);
    leanh::lean_dec(v_a_7453_);
    leanh::lean_dec_ref(v_a_7452_);
    return v_res_7458_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(
    mut v_ev_7465_: *mut leanh::LeanObject,
    mut v_e_7466_: *mut leanh::LeanObject,
    mut v___y_7467_: *mut leanh::LeanObject,
    mut v___y_7468_: *mut leanh::LeanObject,
    mut v___y_7469_: *mut leanh::LeanObject,
    mut v___y_7470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_e_x27_7473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7478_: u8 = 0;
    let mut v___x_7479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7483_: u8 = 0;
    let mut v___x_7484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7488_: u8 = 0;
    let mut v_a_7489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7492_: u8 = 0;
    let mut v___x_7494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7496_: u8 = 0;
    let mut v___x_7497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: u8 = 0;
    let mut v___x_7499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_7500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7502_: u8 = 0;
    let mut v___x_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: u8 = 0;
    let mut v___x_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: u8 = 0;
    let mut v___x_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7497_ = l_Lean_Expr_cleanupAnnotations(v_e_7466_);
                v___x_7498_ = l_Lean_Expr_isApp(v___x_7497_);
                if v___x_7498_ == 0 {
                    leanh::lean_dec_ref(v___x_7497_);
                    leanh::lean_dec_ref(v_ev_7465_);
                    v___x_7499_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                    return v___x_7499_;
                } else {
                    v_arg_7500_ = leanh::lean_ctor_get(v___x_7497_, 1);
                    leanh::lean_inc_ref(v_arg_7500_);
                    v___x_7501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7497_);
                    v___x_7502_ = l_Lean_Expr_isApp(v___x_7501_);
                    if v___x_7502_ == 0 {
                        leanh::lean_dec_ref(v___x_7501_);
                        leanh::lean_dec_ref(v_arg_7500_);
                        leanh::lean_dec_ref(v_ev_7465_);
                        v___x_7503_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                        return v___x_7503_;
                    } else {
                        v___x_7504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7501_);
                        v___x_7505_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__0;
                        v___x_7506_ = l_Lean_Expr_isConstOf(v___x_7504_, v___x_7505_);
                        if v___x_7506_ == 0 {
                            v___x_7507_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___closed__1;
                            v___x_7508_ = l_Lean_Expr_isConstOf(v___x_7504_, v___x_7507_);
                            leanh::lean_dec_ref(v___x_7504_);
                            if v___x_7508_ == 0 {
                                leanh::lean_dec_ref(v_arg_7500_);
                                leanh::lean_dec_ref(v_ev_7465_);
                                v___x_7509_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                                return v___x_7509_;
                            } else {
                                v_e_x27_7473_ = v_arg_7500_;
                                v___y_7474_ = v___y_7467_;
                                v___y_7475_ = v___y_7468_;
                                v___y_7476_ = v___y_7469_;
                                v___y_7477_ = v___y_7470_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_7504_);
                            v_e_x27_7473_ = v_arg_7500_;
                            v___y_7474_ = v___y_7467_;
                            v___y_7475_ = v___y_7468_;
                            v___y_7476_ = v___y_7469_;
                            v___y_7477_ = v___y_7470_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7478_ = 0;
                v___x_7479_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(
                    v_ev_7465_,
                    v_e_x27_7473_,
                    v___x_7478_,
                    v___y_7474_,
                    v___y_7475_,
                    v___y_7476_,
                    v___y_7477_,
                );
                if leanh::lean_obj_tag(v___x_7479_) == 0 {
                    v_a_7480_ = leanh::lean_ctor_get(v___x_7479_, 0);
                    v_isSharedCheck_7488_ = (!leanh::lean_is_exclusive(v___x_7479_)) as u8;
                    if v_isSharedCheck_7488_ == 0 {
                        v___x_7482_ = v___x_7479_;
                        v_isShared_7483_ = v_isSharedCheck_7488_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7480_);
                        leanh::lean_dec(v___x_7479_);
                        v___x_7482_ = leanh::lean_box(0);
                        v_isShared_7483_ = v_isSharedCheck_7488_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7489_ = leanh::lean_ctor_get(v___x_7479_, 0);
                    v_isSharedCheck_7496_ = (!leanh::lean_is_exclusive(v___x_7479_)) as u8;
                    if v_isSharedCheck_7496_ == 0 {
                        v___x_7491_ = v___x_7479_;
                        v_isShared_7492_ = v_isSharedCheck_7496_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7489_);
                        leanh::lean_dec(v___x_7479_);
                        v___x_7491_ = leanh::lean_box(0);
                        v_isShared_7492_ = v_isSharedCheck_7496_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7484_ = lean_array_mk(v_a_7480_);
                if v_isShared_7483_ == 0 {
                    leanh::lean_ctor_set(v___x_7482_, 0, v___x_7484_);
                    v___x_7486_ = v___x_7482_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7487_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7487_, 0, v___x_7484_);
                    v___x_7486_ = v_reuseFailAlloc_7487_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7486_;
            }
            4 => {
                if v_isShared_7492_ == 0 {
                    v___x_7494_ = v___x_7491_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7495_, 0, v_a_7489_);
                    v___x_7494_ = v_reuseFailAlloc_7495_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7494_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed(
    mut v_ev_7510_: *mut leanh::LeanObject,
    mut v_e_7511_: *mut leanh::LeanObject,
    mut v___y_7512_: *mut leanh::LeanObject,
    mut v___y_7513_: *mut leanh::LeanObject,
    mut v___y_7514_: *mut leanh::LeanObject,
    mut v___y_7515_: *mut leanh::LeanObject,
    mut v___y_7516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7517_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0(
        v_ev_7510_,
        v_e_7511_,
        v___y_7512_,
        v___y_7513_,
        v___y_7514_,
        v___y_7515_,
    );
    leanh::lean_dec(v___y_7515_);
    leanh::lean_dec_ref(v___y_7514_);
    leanh::lean_dec(v___y_7513_);
    leanh::lean_dec_ref(v___y_7512_);
    return v_res_7517_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7518_: u8 = 0;
    let mut v___x_7519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7518_ = 0;
    v___x_7519_ = l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__1;
    v___x_7520_ = l_Lean_MessageData_ofConstName(v___x_7519_, v___x_7518_);
    return v___x_7520_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7521_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__0,
    );
    v___x_7522_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_7523_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7523_, 0, v___x_7522_);
    leanh::lean_ctor_set(v___x_7523_, 1, v___x_7521_);
    return v___x_7523_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_7525_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__1,
    );
    v___x_7526_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7526_, 0, v___x_7525_);
    leanh::lean_ctor_set(v___x_7526_, 1, v___x_7524_);
    return v___x_7526_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(
    mut v_ev_7527_: *mut leanh::LeanObject,
    mut v_e_7528_: *mut leanh::LeanObject,
    mut v_a_7529_: *mut leanh::LeanObject,
    mut v_a_7530_: *mut leanh::LeanObject,
    mut v_a_7531_: *mut leanh::LeanObject,
    mut v_a_7532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_7534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7534_ = leanh::lean_alloc_closure(
        l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_7534_, 0, v_ev_7527_);
    v___x_7535_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2_once
        ),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___closed__2,
    );
    v___x_7536_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___f_7534_,
        v_e_7528_,
        v___x_7535_,
        v_a_7529_,
        v_a_7530_,
        v_a_7531_,
        v_a_7532_,
    );
    return v___x_7536_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg___boxed(
    mut v_ev_7537_: *mut leanh::LeanObject,
    mut v_e_7538_: *mut leanh::LeanObject,
    mut v_a_7539_: *mut leanh::LeanObject,
    mut v_a_7540_: *mut leanh::LeanObject,
    mut v_a_7541_: *mut leanh::LeanObject,
    mut v_a_7542_: *mut leanh::LeanObject,
    mut v_a_7543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7544_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(
        v_ev_7537_, v_e_7538_, v_a_7539_, v_a_7540_, v_a_7541_, v_a_7542_,
    );
    leanh::lean_dec(v_a_7542_);
    leanh::lean_dec_ref(v_a_7541_);
    leanh::lean_dec(v_a_7540_);
    leanh::lean_dec_ref(v_a_7539_);
    return v_res_7544_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(
    mut v_00_u03b1_7545_: *mut leanh::LeanObject,
    mut v_ev_7546_: *mut leanh::LeanObject,
    mut v_e_7547_: *mut leanh::LeanObject,
    mut v_a_7548_: *mut leanh::LeanObject,
    mut v_a_7549_: *mut leanh::LeanObject,
    mut v_a_7550_: *mut leanh::LeanObject,
    mut v_a_7551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7553_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___redArg(
        v_ev_7546_, v_e_7547_, v_a_7548_, v_a_7549_, v_a_7550_, v_a_7551_,
    );
    return v___x_7553_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed(
    mut v_00_u03b1_7554_: *mut leanh::LeanObject,
    mut v_ev_7555_: *mut leanh::LeanObject,
    mut v_e_7556_: *mut leanh::LeanObject,
    mut v_a_7557_: *mut leanh::LeanObject,
    mut v_a_7558_: *mut leanh::LeanObject,
    mut v_a_7559_: *mut leanh::LeanObject,
    mut v_a_7560_: *mut leanh::LeanObject,
    mut v_a_7561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7562_ = l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr(
        v_00_u03b1_7554_,
        v_ev_7555_,
        v_e_7556_,
        v_a_7557_,
        v_a_7558_,
        v_a_7559_,
        v_a_7560_,
    );
    leanh::lean_dec(v_a_7560_);
    leanh::lean_dec_ref(v_a_7559_);
    leanh::lean_dec(v_a_7558_);
    leanh::lean_dec_ref(v_a_7557_);
    return v_res_7562_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(
    mut v_e_7563_: *mut leanh::LeanObject,
    mut v_a_7564_: *mut leanh::LeanObject,
    mut v_a_7565_: *mut leanh::LeanObject,
    mut v_a_7566_: *mut leanh::LeanObject,
    mut v_a_7567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7574_: u8 = 0;
    let mut v___x_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7580_: u8 = 0;
    let mut v___x_7582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7584_: u8 = 0;
    let mut v___y_7586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7590_: u8 = 0;
    let mut v___x_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7598_: u8 = 0;
    let mut v___x_7599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7603_: u8 = 0;
    let mut v_a_7604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7607_: u8 = 0;
    let mut v___x_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: u8 = 0;
    let mut v___x_7611_: u8 = 0;
    let mut v_reuseFailAlloc_7612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7613_: u8 = 0;
    let mut v_a_7614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7617_: u8 = 0;
    let mut v___x_7619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7621_: u8 = 0;
    let mut v_a_7622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7625_: u8 = 0;
    let mut v___x_7627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7629_: u8 = 0;
    let mut v___y_7631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7635_: u8 = 0;
    let mut v___x_7636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7643_: u8 = 0;
    let mut v___x_7644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7648_: u8 = 0;
    let mut v_a_7649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7652_: u8 = 0;
    let mut v___x_7654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: u8 = 0;
    let mut v___x_7656_: u8 = 0;
    let mut v_reuseFailAlloc_7657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7658_: u8 = 0;
    let mut v_a_7659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7662_: u8 = 0;
    let mut v___x_7664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7666_: u8 = 0;
    let mut v_a_7667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7670_: u8 = 0;
    let mut v___x_7672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7674_: u8 = 0;
    let mut v___y_7676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7682_: u8 = 0;
    let mut v___x_7683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7690_: u8 = 0;
    let mut v___x_7691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7695_: u8 = 0;
    let mut v_a_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7699_: u8 = 0;
    let mut v___x_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: u8 = 0;
    let mut v___x_7703_: u8 = 0;
    let mut v_reuseFailAlloc_7704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7705_: u8 = 0;
    let mut v_a_7706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7709_: u8 = 0;
    let mut v___x_7711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7713_: u8 = 0;
    let mut v_a_7714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7717_: u8 = 0;
    let mut v___x_7719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7721_: u8 = 0;
    let mut v___y_7723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7729_: u8 = 0;
    let mut v___x_7730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7737_: u8 = 0;
    let mut v___x_7738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7742_: u8 = 0;
    let mut v_a_7743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7746_: u8 = 0;
    let mut v___x_7748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: u8 = 0;
    let mut v___x_7750_: u8 = 0;
    let mut v_reuseFailAlloc_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7752_: u8 = 0;
    let mut v_a_7753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7756_: u8 = 0;
    let mut v___x_7758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7760_: u8 = 0;
    let mut v_a_7761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7764_: u8 = 0;
    let mut v___x_7766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7768_: u8 = 0;
    let mut v___y_7770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7780_: u8 = 0;
    let mut v___x_7781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: u8 = 0;
    let mut v___x_7784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7786_: u8 = 0;
    let mut v_a_7787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7790_: u8 = 0;
    let mut v___x_7792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: u8 = 0;
    let mut v___x_7794_: u8 = 0;
    let mut v_reuseFailAlloc_7795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7796_: u8 = 0;
    let mut v_a_7797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7800_: u8 = 0;
    let mut v___x_7802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7804_: u8 = 0;
    let mut v___x_7805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: u8 = 0;
    let mut v_arg_7807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7810_: u8 = 0;
    let mut v___x_7811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7812_: u8 = 0;
    let mut v___x_7813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7814_: u8 = 0;
    let mut v___x_7815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7816_: u8 = 0;
    let mut v___x_7817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: u8 = 0;
    let mut v___x_7819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7823_: u8 = 0;
    let mut v___x_7824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: u8 = 0;
    let mut v___x_7827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7829_: u8 = 0;
    let mut v_a_7830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7833_: u8 = 0;
    let mut v___x_7835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7837_: u8 = 0;
    let mut v___x_7838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7842_: u8 = 0;
    let mut v___x_7843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7847_: u8 = 0;
    let mut v_a_7848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7851_: u8 = 0;
    let mut v___x_7853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7855_: u8 = 0;
    let mut v___x_7856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7860_: u8 = 0;
    let mut v___x_7861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7865_: u8 = 0;
    let mut v_a_7866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7869_: u8 = 0;
    let mut v___x_7871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7873_: u8 = 0;
    let mut v___x_7874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7878_: u8 = 0;
    let mut v___x_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7883_: u8 = 0;
    let mut v_a_7884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7887_: u8 = 0;
    let mut v___x_7889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7891_: u8 = 0;
    let mut v___x_7892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7896_: u8 = 0;
    let mut v___x_7897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7901_: u8 = 0;
    let mut v_a_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7905_: u8 = 0;
    let mut v___x_7907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_7563_);
                v___x_7805_ = l_Lean_Expr_cleanupAnnotations(v_e_7563_);
                v___x_7806_ = l_Lean_Expr_isApp(v___x_7805_);
                if v___x_7806_ == 0 {
                    leanh::lean_dec_ref(v___x_7805_);
                    v___y_7770_ = v_a_7564_;
                    v___y_7771_ = v_a_7565_;
                    v___y_7772_ = v_a_7566_;
                    v___y_7773_ = v_a_7567_;
                    state = 40;
                    continue;
                } else {
                    v_arg_7807_ = leanh::lean_ctor_get(v___x_7805_, 1);
                    leanh::lean_inc_ref(v_arg_7807_);
                    v___x_7808_ = l_Lean_Expr_appFnCleanup___redArg(v___x_7805_);
                    v___x_7809_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__8;
                    v___x_7810_ = l_Lean_Expr_isConstOf(v___x_7808_, v___x_7809_);
                    if v___x_7810_ == 0 {
                        v___x_7811_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__10;
                        v___x_7812_ = l_Lean_Expr_isConstOf(v___x_7808_, v___x_7811_);
                        if v___x_7812_ == 0 {
                            v___x_7813_ =
                                l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__13;
                            v___x_7814_ = l_Lean_Expr_isConstOf(v___x_7808_, v___x_7813_);
                            if v___x_7814_ == 0 {
                                v___x_7815_ =
                                    l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__15;
                                v___x_7816_ = l_Lean_Expr_isConstOf(v___x_7808_, v___x_7815_);
                                if v___x_7816_ == 0 {
                                    v___x_7817_ = l_Lean_Elab_ConfigEval_EvalTerm_evalDataValueStx___closed__3;
                                    v___x_7818_ = l_Lean_Expr_isConstOf(v___x_7808_, v___x_7817_);
                                    leanh::lean_dec_ref(v___x_7808_);
                                    if v___x_7818_ == 0 {
                                        leanh::lean_dec_ref(v_arg_7807_);
                                        v___y_7770_ = v_a_7564_;
                                        v___y_7771_ = v_a_7565_;
                                        v___y_7772_ = v_a_7566_;
                                        v___y_7773_ = v_a_7567_;
                                        state = 40;
                                        continue;
                                    } else {
                                        leanh::lean_dec_ref(v_e_7563_);
                                        v___x_7819_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                            v_arg_7807_,
                                            v_a_7564_,
                                            v_a_7565_,
                                            v_a_7566_,
                                            v_a_7567_,
                                        );
                                        if leanh::lean_obj_tag(v___x_7819_) == 0 {
                                            v_a_7820_ = leanh::lean_ctor_get(v___x_7819_, 0);
                                            v_isSharedCheck_7829_ =
                                                (!leanh::lean_is_exclusive(v___x_7819_))
                                                    as u8;
                                            if v_isSharedCheck_7829_ == 0 {
                                                v___x_7822_ = v___x_7819_;
                                                v_isShared_7823_ = v_isSharedCheck_7829_;
                                                state = 47;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_7820_);
                                                leanh::lean_dec(v___x_7819_);
                                                v___x_7822_ = leanh::lean_box(0);
                                                v_isShared_7823_ = v_isSharedCheck_7829_;
                                                state = 47;
                                                continue;
                                            }
                                        } else {
                                            v_a_7830_ = leanh::lean_ctor_get(v___x_7819_, 0);
                                            v_isSharedCheck_7837_ =
                                                (!leanh::lean_is_exclusive(v___x_7819_))
                                                    as u8;
                                            if v_isSharedCheck_7837_ == 0 {
                                                v___x_7832_ = v___x_7819_;
                                                v_isShared_7833_ = v_isSharedCheck_7837_;
                                                state = 49;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_7830_);
                                                leanh::lean_dec(v___x_7819_);
                                                v___x_7832_ = leanh::lean_box(0);
                                                v_isShared_7833_ = v_isSharedCheck_7837_;
                                                state = 49;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_7808_);
                                    leanh::lean_dec_ref(v_e_7563_);
                                    v___x_7838_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNatExpr(
                                        v_arg_7807_,
                                        v_a_7564_,
                                        v_a_7565_,
                                        v_a_7566_,
                                        v_a_7567_,
                                    );
                                    if leanh::lean_obj_tag(v___x_7838_) == 0 {
                                        v_a_7839_ = leanh::lean_ctor_get(v___x_7838_, 0);
                                        v_isSharedCheck_7847_ =
                                            (!leanh::lean_is_exclusive(v___x_7838_)) as u8;
                                        if v_isSharedCheck_7847_ == 0 {
                                            v___x_7841_ = v___x_7838_;
                                            v_isShared_7842_ = v_isSharedCheck_7847_;
                                            state = 51;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_7839_);
                                            leanh::lean_dec(v___x_7838_);
                                            v___x_7841_ = leanh::lean_box(0);
                                            v_isShared_7842_ = v_isSharedCheck_7847_;
                                            state = 51;
                                            continue;
                                        }
                                    } else {
                                        v_a_7848_ = leanh::lean_ctor_get(v___x_7838_, 0);
                                        v_isSharedCheck_7855_ =
                                            (!leanh::lean_is_exclusive(v___x_7838_)) as u8;
                                        if v_isSharedCheck_7855_ == 0 {
                                            v___x_7850_ = v___x_7838_;
                                            v_isShared_7851_ = v_isSharedCheck_7855_;
                                            state = 53;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_7848_);
                                            leanh::lean_dec(v___x_7838_);
                                            v___x_7850_ = leanh::lean_box(0);
                                            v_isShared_7851_ = v_isSharedCheck_7855_;
                                            state = 53;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_7808_);
                                leanh::lean_dec_ref(v_e_7563_);
                                v___x_7856_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExpr(
                                    v_arg_7807_,
                                    v_a_7564_,
                                    v_a_7565_,
                                    v_a_7566_,
                                    v_a_7567_,
                                );
                                if leanh::lean_obj_tag(v___x_7856_) == 0 {
                                    v_a_7857_ = leanh::lean_ctor_get(v___x_7856_, 0);
                                    v_isSharedCheck_7865_ =
                                        (!leanh::lean_is_exclusive(v___x_7856_)) as u8;
                                    if v_isSharedCheck_7865_ == 0 {
                                        v___x_7859_ = v___x_7856_;
                                        v_isShared_7860_ = v_isSharedCheck_7865_;
                                        state = 55;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7857_);
                                        leanh::lean_dec(v___x_7856_);
                                        v___x_7859_ = leanh::lean_box(0);
                                        v_isShared_7860_ = v_isSharedCheck_7865_;
                                        state = 55;
                                        continue;
                                    }
                                } else {
                                    v_a_7866_ = leanh::lean_ctor_get(v___x_7856_, 0);
                                    v_isSharedCheck_7873_ =
                                        (!leanh::lean_is_exclusive(v___x_7856_)) as u8;
                                    if v_isSharedCheck_7873_ == 0 {
                                        v___x_7868_ = v___x_7856_;
                                        v_isShared_7869_ = v_isSharedCheck_7873_;
                                        state = 57;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7866_);
                                        leanh::lean_dec(v___x_7856_);
                                        v___x_7868_ = leanh::lean_box(0);
                                        v_isShared_7869_ = v_isSharedCheck_7873_;
                                        state = 57;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_7808_);
                            leanh::lean_dec_ref(v_e_7563_);
                            v___x_7874_ = l_Lean_Elab_ConfigEval_EvalExpr_evalStringExpr(
                                v_arg_7807_,
                                v_a_7564_,
                                v_a_7565_,
                                v_a_7566_,
                                v_a_7567_,
                            );
                            if leanh::lean_obj_tag(v___x_7874_) == 0 {
                                v_a_7875_ = leanh::lean_ctor_get(v___x_7874_, 0);
                                v_isSharedCheck_7883_ =
                                    (!leanh::lean_is_exclusive(v___x_7874_)) as u8;
                                if v_isSharedCheck_7883_ == 0 {
                                    v___x_7877_ = v___x_7874_;
                                    v_isShared_7878_ = v_isSharedCheck_7883_;
                                    state = 59;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7875_);
                                    leanh::lean_dec(v___x_7874_);
                                    v___x_7877_ = leanh::lean_box(0);
                                    v_isShared_7878_ = v_isSharedCheck_7883_;
                                    state = 59;
                                    continue;
                                }
                            } else {
                                v_a_7884_ = leanh::lean_ctor_get(v___x_7874_, 0);
                                v_isSharedCheck_7891_ =
                                    (!leanh::lean_is_exclusive(v___x_7874_)) as u8;
                                if v_isSharedCheck_7891_ == 0 {
                                    v___x_7886_ = v___x_7874_;
                                    v_isShared_7887_ = v_isSharedCheck_7891_;
                                    state = 61;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7884_);
                                    leanh::lean_dec(v___x_7874_);
                                    v___x_7886_ = leanh::lean_box(0);
                                    v_isShared_7887_ = v_isSharedCheck_7891_;
                                    state = 61;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_7808_);
                        leanh::lean_dec_ref(v_e_7563_);
                        v___x_7892_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExpr(
                            v_arg_7807_,
                            v_a_7564_,
                            v_a_7565_,
                            v_a_7566_,
                            v_a_7567_,
                        );
                        if leanh::lean_obj_tag(v___x_7892_) == 0 {
                            v_a_7893_ = leanh::lean_ctor_get(v___x_7892_, 0);
                            v_isSharedCheck_7901_ =
                                (!leanh::lean_is_exclusive(v___x_7892_)) as u8;
                            if v_isSharedCheck_7901_ == 0 {
                                v___x_7895_ = v___x_7892_;
                                v_isShared_7896_ = v_isSharedCheck_7901_;
                                state = 63;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7893_);
                                leanh::lean_dec(v___x_7892_);
                                v___x_7895_ = leanh::lean_box(0);
                                v_isShared_7896_ = v_isSharedCheck_7901_;
                                state = 63;
                                continue;
                            }
                        } else {
                            v_a_7902_ = leanh::lean_ctor_get(v___x_7892_, 0);
                            v_isSharedCheck_7909_ =
                                (!leanh::lean_is_exclusive(v___x_7892_)) as u8;
                            if v_isSharedCheck_7909_ == 0 {
                                v___x_7904_ = v___x_7892_;
                                v_isShared_7905_ = v_isSharedCheck_7909_;
                                state = 65;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7902_);
                                leanh::lean_dec(v___x_7892_);
                                v___x_7904_ = leanh::lean_box(0);
                                v_isShared_7905_ = v_isSharedCheck_7909_;
                                state = 65;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v___y_7574_ == 0 {
                    leanh::lean_dec_ref(v___y_7570_);
                    v___x_7575_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_7573_,
                        v___y_7572_,
                        v___y_7571_,
                    );
                    leanh::lean_dec_ref(v___y_7573_);
                    if leanh::lean_obj_tag(v___x_7575_) == 0 {
                        leanh::lean_dec_ref_known(v___x_7575_, 1);
                        v___x_7576_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore_spec__0___redArg();
                        return v___x_7576_;
                    } else {
                        v_a_7577_ = leanh::lean_ctor_get(v___x_7575_, 0);
                        v_isSharedCheck_7584_ =
                            (!leanh::lean_is_exclusive(v___x_7575_)) as u8;
                        if v_isSharedCheck_7584_ == 0 {
                            v___x_7579_ = v___x_7575_;
                            v_isShared_7580_ = v_isSharedCheck_7584_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7577_);
                            leanh::lean_dec(v___x_7575_);
                            v___x_7579_ = leanh::lean_box(0);
                            v_isShared_7580_ = v_isSharedCheck_7584_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_7573_);
                    return v___y_7570_;
                }
            }
            2 => {
                if v_isShared_7580_ == 0 {
                    v___x_7582_ = v___x_7579_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7583_, 0, v_a_7577_);
                    v___x_7582_ = v_reuseFailAlloc_7583_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7582_;
            }
            4 => {
                if v___y_7590_ == 0 {
                    leanh::lean_dec_ref(v___y_7586_);
                    v___x_7591_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_7587_,
                        v___y_7589_,
                        v___y_7588_,
                    );
                    leanh::lean_dec_ref(v___y_7587_);
                    if leanh::lean_obj_tag(v___x_7591_) == 0 {
                        leanh::lean_dec_ref_known(v___x_7591_, 1);
                        v___x_7592_ = l_Lean_Meta_saveState___redArg(v___y_7589_, v___y_7588_);
                        if leanh::lean_obj_tag(v___x_7592_) == 0 {
                            v_a_7593_ = leanh::lean_ctor_get(v___x_7592_, 0);
                            leanh::lean_inc(v_a_7593_);
                            leanh::lean_dec_ref_known(v___x_7592_, 1);
                            v___x_7594_ = l_Lean_Elab_ConfigEval_EvalExpr_evalNameExprCore___redArg(
                                v_e_7563_,
                            );
                            if leanh::lean_obj_tag(v___x_7594_) == 0 {
                                leanh::lean_dec(v_a_7593_);
                                v_a_7595_ = leanh::lean_ctor_get(v___x_7594_, 0);
                                v_isSharedCheck_7603_ =
                                    (!leanh::lean_is_exclusive(v___x_7594_)) as u8;
                                if v_isSharedCheck_7603_ == 0 {
                                    v___x_7597_ = v___x_7594_;
                                    v_isShared_7598_ = v_isSharedCheck_7603_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7595_);
                                    leanh::lean_dec(v___x_7594_);
                                    v___x_7597_ = leanh::lean_box(0);
                                    v_isShared_7598_ = v_isSharedCheck_7603_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_7604_ = leanh::lean_ctor_get(v___x_7594_, 0);
                                v_isSharedCheck_7613_ =
                                    (!leanh::lean_is_exclusive(v___x_7594_)) as u8;
                                if v_isSharedCheck_7613_ == 0 {
                                    v___x_7606_ = v___x_7594_;
                                    v_isShared_7607_ = v_isSharedCheck_7613_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7604_);
                                    leanh::lean_dec(v___x_7594_);
                                    v___x_7606_ = leanh::lean_box(0);
                                    v_isShared_7607_ = v_isSharedCheck_7613_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_7563_);
                            v_a_7614_ = leanh::lean_ctor_get(v___x_7592_, 0);
                            v_isSharedCheck_7621_ =
                                (!leanh::lean_is_exclusive(v___x_7592_)) as u8;
                            if v_isSharedCheck_7621_ == 0 {
                                v___x_7616_ = v___x_7592_;
                                v_isShared_7617_ = v_isSharedCheck_7621_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7614_);
                                leanh::lean_dec(v___x_7592_);
                                v___x_7616_ = leanh::lean_box(0);
                                v_isShared_7617_ = v_isSharedCheck_7621_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7563_);
                        v_a_7622_ = leanh::lean_ctor_get(v___x_7591_, 0);
                        v_isSharedCheck_7629_ =
                            (!leanh::lean_is_exclusive(v___x_7591_)) as u8;
                        if v_isSharedCheck_7629_ == 0 {
                            v___x_7624_ = v___x_7591_;
                            v_isShared_7625_ = v_isSharedCheck_7629_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7622_);
                            leanh::lean_dec(v___x_7591_);
                            v___x_7624_ = leanh::lean_box(0);
                            v_isShared_7625_ = v_isSharedCheck_7629_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_7587_);
                    leanh::lean_dec_ref(v_e_7563_);
                    return v___y_7586_;
                }
            }
            5 => {
                v___x_7599_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7599_, 0, v_a_7595_);
                if v_isShared_7598_ == 0 {
                    leanh::lean_ctor_set(v___x_7597_, 0, v___x_7599_);
                    v___x_7601_ = v___x_7597_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7602_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7602_, 0, v___x_7599_);
                    v___x_7601_ = v_reuseFailAlloc_7602_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7601_;
            }
            7 => {
                leanh::lean_inc(v_a_7604_);
                if v_isShared_7607_ == 0 {
                    v___x_7609_ = v___x_7606_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7612_, 0, v_a_7604_);
                    v___x_7609_ = v_reuseFailAlloc_7612_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7610_ = l_Lean_Exception_isInterrupt(v_a_7604_);
                if v___x_7610_ == 0 {
                    v___x_7611_ = l_Lean_Exception_isRuntime(v_a_7604_);
                    v___y_7570_ = v___x_7609_;
                    v___y_7571_ = v___y_7588_;
                    v___y_7572_ = v___y_7589_;
                    v___y_7573_ = v_a_7593_;
                    v___y_7574_ = v___x_7611_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7604_);
                    v___y_7570_ = v___x_7609_;
                    v___y_7571_ = v___y_7588_;
                    v___y_7572_ = v___y_7589_;
                    v___y_7573_ = v_a_7593_;
                    v___y_7574_ = v___x_7610_;
                    state = 1;
                    continue;
                }
            }
            9 => {
                if v_isShared_7617_ == 0 {
                    v___x_7619_ = v___x_7616_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7620_, 0, v_a_7614_);
                    v___x_7619_ = v_reuseFailAlloc_7620_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7619_;
            }
            11 => {
                if v_isShared_7625_ == 0 {
                    v___x_7627_ = v___x_7624_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7628_, 0, v_a_7622_);
                    v___x_7627_ = v_reuseFailAlloc_7628_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7627_;
            }
            13 => {
                if v___y_7635_ == 0 {
                    leanh::lean_dec_ref(v___y_7631_);
                    v___x_7636_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_7632_,
                        v___y_7634_,
                        v___y_7633_,
                    );
                    leanh::lean_dec_ref(v___y_7632_);
                    if leanh::lean_obj_tag(v___x_7636_) == 0 {
                        leanh::lean_dec_ref_known(v___x_7636_, 1);
                        v___x_7637_ = l_Lean_Meta_saveState___redArg(v___y_7634_, v___y_7633_);
                        if leanh::lean_obj_tag(v___x_7637_) == 0 {
                            v_a_7638_ = leanh::lean_ctor_get(v___x_7637_, 0);
                            leanh::lean_inc(v_a_7638_);
                            leanh::lean_dec_ref_known(v___x_7637_, 1);
                            leanh::lean_inc_ref(v_e_7563_);
                            v___x_7639_ =
                                l_Lean_Elab_ConfigEval_EvalExpr_evalStringExprCore___redArg(
                                    v_e_7563_,
                                );
                            if leanh::lean_obj_tag(v___x_7639_) == 0 {
                                leanh::lean_dec(v_a_7638_);
                                leanh::lean_dec_ref(v_e_7563_);
                                v_a_7640_ = leanh::lean_ctor_get(v___x_7639_, 0);
                                v_isSharedCheck_7648_ =
                                    (!leanh::lean_is_exclusive(v___x_7639_)) as u8;
                                if v_isSharedCheck_7648_ == 0 {
                                    v___x_7642_ = v___x_7639_;
                                    v_isShared_7643_ = v_isSharedCheck_7648_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7640_);
                                    leanh::lean_dec(v___x_7639_);
                                    v___x_7642_ = leanh::lean_box(0);
                                    v_isShared_7643_ = v_isSharedCheck_7648_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                v_a_7649_ = leanh::lean_ctor_get(v___x_7639_, 0);
                                v_isSharedCheck_7658_ =
                                    (!leanh::lean_is_exclusive(v___x_7639_)) as u8;
                                if v_isSharedCheck_7658_ == 0 {
                                    v___x_7651_ = v___x_7639_;
                                    v_isShared_7652_ = v_isSharedCheck_7658_;
                                    state = 16;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7649_);
                                    leanh::lean_dec(v___x_7639_);
                                    v___x_7651_ = leanh::lean_box(0);
                                    v_isShared_7652_ = v_isSharedCheck_7658_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_7563_);
                            v_a_7659_ = leanh::lean_ctor_get(v___x_7637_, 0);
                            v_isSharedCheck_7666_ =
                                (!leanh::lean_is_exclusive(v___x_7637_)) as u8;
                            if v_isSharedCheck_7666_ == 0 {
                                v___x_7661_ = v___x_7637_;
                                v_isShared_7662_ = v_isSharedCheck_7666_;
                                state = 18;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7659_);
                                leanh::lean_dec(v___x_7637_);
                                v___x_7661_ = leanh::lean_box(0);
                                v_isShared_7662_ = v_isSharedCheck_7666_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7563_);
                        v_a_7667_ = leanh::lean_ctor_get(v___x_7636_, 0);
                        v_isSharedCheck_7674_ =
                            (!leanh::lean_is_exclusive(v___x_7636_)) as u8;
                        if v_isSharedCheck_7674_ == 0 {
                            v___x_7669_ = v___x_7636_;
                            v_isShared_7670_ = v_isSharedCheck_7674_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7667_);
                            leanh::lean_dec(v___x_7636_);
                            v___x_7669_ = leanh::lean_box(0);
                            v_isShared_7670_ = v_isSharedCheck_7674_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_7632_);
                    leanh::lean_dec_ref(v_e_7563_);
                    return v___y_7631_;
                }
            }
            14 => {
                v___x_7644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7644_, 0, v_a_7640_);
                if v_isShared_7643_ == 0 {
                    leanh::lean_ctor_set(v___x_7642_, 0, v___x_7644_);
                    v___x_7646_ = v___x_7642_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7647_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7647_, 0, v___x_7644_);
                    v___x_7646_ = v_reuseFailAlloc_7647_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7646_;
            }
            16 => {
                leanh::lean_inc(v_a_7649_);
                if v_isShared_7652_ == 0 {
                    v___x_7654_ = v___x_7651_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7657_, 0, v_a_7649_);
                    v___x_7654_ = v_reuseFailAlloc_7657_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_7655_ = l_Lean_Exception_isInterrupt(v_a_7649_);
                if v___x_7655_ == 0 {
                    v___x_7656_ = l_Lean_Exception_isRuntime(v_a_7649_);
                    v___y_7586_ = v___x_7654_;
                    v___y_7587_ = v_a_7638_;
                    v___y_7588_ = v___y_7633_;
                    v___y_7589_ = v___y_7634_;
                    v___y_7590_ = v___x_7656_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7649_);
                    v___y_7586_ = v___x_7654_;
                    v___y_7587_ = v_a_7638_;
                    v___y_7588_ = v___y_7633_;
                    v___y_7589_ = v___y_7634_;
                    v___y_7590_ = v___x_7655_;
                    state = 4;
                    continue;
                }
            }
            18 => {
                if v_isShared_7662_ == 0 {
                    v___x_7664_ = v___x_7661_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7665_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7665_, 0, v_a_7659_);
                    v___x_7664_ = v_reuseFailAlloc_7665_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7664_;
            }
            20 => {
                if v_isShared_7670_ == 0 {
                    v___x_7672_ = v___x_7669_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7673_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7673_, 0, v_a_7667_);
                    v___x_7672_ = v_reuseFailAlloc_7673_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7672_;
            }
            22 => {
                if v___y_7682_ == 0 {
                    leanh::lean_dec_ref(v___y_7678_);
                    v___x_7683_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_7681_,
                        v___y_7679_,
                        v___y_7677_,
                    );
                    leanh::lean_dec_ref(v___y_7681_);
                    if leanh::lean_obj_tag(v___x_7683_) == 0 {
                        leanh::lean_dec_ref_known(v___x_7683_, 1);
                        v___x_7684_ = l_Lean_Meta_saveState___redArg(v___y_7679_, v___y_7677_);
                        if leanh::lean_obj_tag(v___x_7684_) == 0 {
                            v_a_7685_ = leanh::lean_ctor_get(v___x_7684_, 0);
                            leanh::lean_inc(v_a_7685_);
                            leanh::lean_dec_ref_known(v___x_7684_, 1);
                            leanh::lean_inc_ref(v_e_7563_);
                            v___x_7686_ = l_Lean_Elab_ConfigEval_EvalExpr_evalIntExprCore(
                                v_e_7563_,
                                v___y_7680_,
                                v___y_7679_,
                                v___y_7676_,
                                v___y_7677_,
                            );
                            if leanh::lean_obj_tag(v___x_7686_) == 0 {
                                leanh::lean_dec(v_a_7685_);
                                leanh::lean_dec_ref(v_e_7563_);
                                v_a_7687_ = leanh::lean_ctor_get(v___x_7686_, 0);
                                v_isSharedCheck_7695_ =
                                    (!leanh::lean_is_exclusive(v___x_7686_)) as u8;
                                if v_isSharedCheck_7695_ == 0 {
                                    v___x_7689_ = v___x_7686_;
                                    v_isShared_7690_ = v_isSharedCheck_7695_;
                                    state = 23;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7687_);
                                    leanh::lean_dec(v___x_7686_);
                                    v___x_7689_ = leanh::lean_box(0);
                                    v_isShared_7690_ = v_isSharedCheck_7695_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_a_7696_ = leanh::lean_ctor_get(v___x_7686_, 0);
                                v_isSharedCheck_7705_ =
                                    (!leanh::lean_is_exclusive(v___x_7686_)) as u8;
                                if v_isSharedCheck_7705_ == 0 {
                                    v___x_7698_ = v___x_7686_;
                                    v_isShared_7699_ = v_isSharedCheck_7705_;
                                    state = 25;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7696_);
                                    leanh::lean_dec(v___x_7686_);
                                    v___x_7698_ = leanh::lean_box(0);
                                    v_isShared_7699_ = v_isSharedCheck_7705_;
                                    state = 25;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_7563_);
                            v_a_7706_ = leanh::lean_ctor_get(v___x_7684_, 0);
                            v_isSharedCheck_7713_ =
                                (!leanh::lean_is_exclusive(v___x_7684_)) as u8;
                            if v_isSharedCheck_7713_ == 0 {
                                v___x_7708_ = v___x_7684_;
                                v_isShared_7709_ = v_isSharedCheck_7713_;
                                state = 27;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7706_);
                                leanh::lean_dec(v___x_7684_);
                                v___x_7708_ = leanh::lean_box(0);
                                v_isShared_7709_ = v_isSharedCheck_7713_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7563_);
                        v_a_7714_ = leanh::lean_ctor_get(v___x_7683_, 0);
                        v_isSharedCheck_7721_ =
                            (!leanh::lean_is_exclusive(v___x_7683_)) as u8;
                        if v_isSharedCheck_7721_ == 0 {
                            v___x_7716_ = v___x_7683_;
                            v_isShared_7717_ = v_isSharedCheck_7721_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7714_);
                            leanh::lean_dec(v___x_7683_);
                            v___x_7716_ = leanh::lean_box(0);
                            v_isShared_7717_ = v_isSharedCheck_7721_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_7681_);
                    leanh::lean_dec_ref(v_e_7563_);
                    return v___y_7678_;
                }
            }
            23 => {
                v___x_7691_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7691_, 0, v_a_7687_);
                if v_isShared_7690_ == 0 {
                    leanh::lean_ctor_set(v___x_7689_, 0, v___x_7691_);
                    v___x_7693_ = v___x_7689_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7694_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7694_, 0, v___x_7691_);
                    v___x_7693_ = v_reuseFailAlloc_7694_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7693_;
            }
            25 => {
                leanh::lean_inc(v_a_7696_);
                if v_isShared_7699_ == 0 {
                    v___x_7701_ = v___x_7698_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_7704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7704_, 0, v_a_7696_);
                    v___x_7701_ = v_reuseFailAlloc_7704_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_7702_ = l_Lean_Exception_isInterrupt(v_a_7696_);
                if v___x_7702_ == 0 {
                    v___x_7703_ = l_Lean_Exception_isRuntime(v_a_7696_);
                    v___y_7631_ = v___x_7701_;
                    v___y_7632_ = v_a_7685_;
                    v___y_7633_ = v___y_7677_;
                    v___y_7634_ = v___y_7679_;
                    v___y_7635_ = v___x_7703_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7696_);
                    v___y_7631_ = v___x_7701_;
                    v___y_7632_ = v_a_7685_;
                    v___y_7633_ = v___y_7677_;
                    v___y_7634_ = v___y_7679_;
                    v___y_7635_ = v___x_7702_;
                    state = 13;
                    continue;
                }
            }
            27 => {
                if v_isShared_7709_ == 0 {
                    v___x_7711_ = v___x_7708_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7712_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7712_, 0, v_a_7706_);
                    v___x_7711_ = v_reuseFailAlloc_7712_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_7711_;
            }
            29 => {
                if v_isShared_7717_ == 0 {
                    v___x_7719_ = v___x_7716_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_7720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7720_, 0, v_a_7714_);
                    v___x_7719_ = v_reuseFailAlloc_7720_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_7719_;
            }
            31 => {
                if v___y_7729_ == 0 {
                    leanh::lean_dec_ref(v___y_7724_);
                    v___x_7730_ = l_Lean_Meta_SavedState_restore___redArg(
                        v___y_7725_,
                        v___y_7727_,
                        v___y_7726_,
                    );
                    leanh::lean_dec_ref(v___y_7725_);
                    if leanh::lean_obj_tag(v___x_7730_) == 0 {
                        leanh::lean_dec_ref_known(v___x_7730_, 1);
                        v___x_7731_ = l_Lean_Meta_saveState___redArg(v___y_7727_, v___y_7726_);
                        if leanh::lean_obj_tag(v___x_7731_) == 0 {
                            v_a_7732_ = leanh::lean_ctor_get(v___x_7731_, 0);
                            leanh::lean_inc(v_a_7732_);
                            leanh::lean_dec_ref_known(v___x_7731_, 1);
                            leanh::lean_inc_ref(v_e_7563_);
                            v___x_7733_ =
                                l_Lean_Elab_ConfigEval_EvalExpr_evalNatExprCore___redArg(v_e_7563_);
                            if leanh::lean_obj_tag(v___x_7733_) == 0 {
                                leanh::lean_dec(v_a_7732_);
                                leanh::lean_dec_ref(v_e_7563_);
                                v_a_7734_ = leanh::lean_ctor_get(v___x_7733_, 0);
                                v_isSharedCheck_7742_ =
                                    (!leanh::lean_is_exclusive(v___x_7733_)) as u8;
                                if v_isSharedCheck_7742_ == 0 {
                                    v___x_7736_ = v___x_7733_;
                                    v_isShared_7737_ = v_isSharedCheck_7742_;
                                    state = 32;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7734_);
                                    leanh::lean_dec(v___x_7733_);
                                    v___x_7736_ = leanh::lean_box(0);
                                    v_isShared_7737_ = v_isSharedCheck_7742_;
                                    state = 32;
                                    continue;
                                }
                            } else {
                                v_a_7743_ = leanh::lean_ctor_get(v___x_7733_, 0);
                                v_isSharedCheck_7752_ =
                                    (!leanh::lean_is_exclusive(v___x_7733_)) as u8;
                                if v_isSharedCheck_7752_ == 0 {
                                    v___x_7745_ = v___x_7733_;
                                    v_isShared_7746_ = v_isSharedCheck_7752_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_7743_);
                                    leanh::lean_dec(v___x_7733_);
                                    v___x_7745_ = leanh::lean_box(0);
                                    v_isShared_7746_ = v_isSharedCheck_7752_;
                                    state = 34;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_7563_);
                            v_a_7753_ = leanh::lean_ctor_get(v___x_7731_, 0);
                            v_isSharedCheck_7760_ =
                                (!leanh::lean_is_exclusive(v___x_7731_)) as u8;
                            if v_isSharedCheck_7760_ == 0 {
                                v___x_7755_ = v___x_7731_;
                                v_isShared_7756_ = v_isSharedCheck_7760_;
                                state = 36;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7753_);
                                leanh::lean_dec(v___x_7731_);
                                v___x_7755_ = leanh::lean_box(0);
                                v_isShared_7756_ = v_isSharedCheck_7760_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7563_);
                        v_a_7761_ = leanh::lean_ctor_get(v___x_7730_, 0);
                        v_isSharedCheck_7768_ =
                            (!leanh::lean_is_exclusive(v___x_7730_)) as u8;
                        if v_isSharedCheck_7768_ == 0 {
                            v___x_7763_ = v___x_7730_;
                            v_isShared_7764_ = v_isSharedCheck_7768_;
                            state = 38;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7761_);
                            leanh::lean_dec(v___x_7730_);
                            v___x_7763_ = leanh::lean_box(0);
                            v_isShared_7764_ = v_isSharedCheck_7768_;
                            state = 38;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_7725_);
                    leanh::lean_dec_ref(v_e_7563_);
                    return v___y_7724_;
                }
            }
            32 => {
                v___x_7738_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7738_, 0, v_a_7734_);
                if v_isShared_7737_ == 0 {
                    leanh::lean_ctor_set(v___x_7736_, 0, v___x_7738_);
                    v___x_7740_ = v___x_7736_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7741_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7741_, 0, v___x_7738_);
                    v___x_7740_ = v_reuseFailAlloc_7741_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7740_;
            }
            34 => {
                leanh::lean_inc(v_a_7743_);
                if v_isShared_7746_ == 0 {
                    v___x_7748_ = v___x_7745_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_7751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7751_, 0, v_a_7743_);
                    v___x_7748_ = v_reuseFailAlloc_7751_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_7749_ = l_Lean_Exception_isInterrupt(v_a_7743_);
                if v___x_7749_ == 0 {
                    v___x_7750_ = l_Lean_Exception_isRuntime(v_a_7743_);
                    v___y_7676_ = v___y_7723_;
                    v___y_7677_ = v___y_7726_;
                    v___y_7678_ = v___x_7748_;
                    v___y_7679_ = v___y_7727_;
                    v___y_7680_ = v___y_7728_;
                    v___y_7681_ = v_a_7732_;
                    v___y_7682_ = v___x_7750_;
                    state = 22;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7743_);
                    v___y_7676_ = v___y_7723_;
                    v___y_7677_ = v___y_7726_;
                    v___y_7678_ = v___x_7748_;
                    v___y_7679_ = v___y_7727_;
                    v___y_7680_ = v___y_7728_;
                    v___y_7681_ = v_a_7732_;
                    v___y_7682_ = v___x_7749_;
                    state = 22;
                    continue;
                }
            }
            36 => {
                if v_isShared_7756_ == 0 {
                    v___x_7758_ = v___x_7755_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_7759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7759_, 0, v_a_7753_);
                    v___x_7758_ = v_reuseFailAlloc_7759_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_7758_;
            }
            38 => {
                if v_isShared_7764_ == 0 {
                    v___x_7766_ = v___x_7763_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_7767_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7767_, 0, v_a_7761_);
                    v___x_7766_ = v_reuseFailAlloc_7767_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_7766_;
            }
            40 => {
                v___x_7774_ = l_Lean_Meta_saveState___redArg(v___y_7771_, v___y_7773_);
                if leanh::lean_obj_tag(v___x_7774_) == 0 {
                    v_a_7775_ = leanh::lean_ctor_get(v___x_7774_, 0);
                    leanh::lean_inc(v_a_7775_);
                    leanh::lean_dec_ref_known(v___x_7774_, 1);
                    leanh::lean_inc_ref(v_e_7563_);
                    v___x_7776_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExprCore(
                        v_e_7563_,
                        v___y_7770_,
                        v___y_7771_,
                        v___y_7772_,
                        v___y_7773_,
                    );
                    if leanh::lean_obj_tag(v___x_7776_) == 0 {
                        leanh::lean_dec(v_a_7775_);
                        leanh::lean_dec_ref(v_e_7563_);
                        v_a_7777_ = leanh::lean_ctor_get(v___x_7776_, 0);
                        v_isSharedCheck_7786_ =
                            (!leanh::lean_is_exclusive(v___x_7776_)) as u8;
                        if v_isSharedCheck_7786_ == 0 {
                            v___x_7779_ = v___x_7776_;
                            v_isShared_7780_ = v_isSharedCheck_7786_;
                            state = 41;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7777_);
                            leanh::lean_dec(v___x_7776_);
                            v___x_7779_ = leanh::lean_box(0);
                            v_isShared_7780_ = v_isSharedCheck_7786_;
                            state = 41;
                            continue;
                        }
                    } else {
                        v_a_7787_ = leanh::lean_ctor_get(v___x_7776_, 0);
                        v_isSharedCheck_7796_ =
                            (!leanh::lean_is_exclusive(v___x_7776_)) as u8;
                        if v_isSharedCheck_7796_ == 0 {
                            v___x_7789_ = v___x_7776_;
                            v_isShared_7790_ = v_isSharedCheck_7796_;
                            state = 43;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7787_);
                            leanh::lean_dec(v___x_7776_);
                            v___x_7789_ = leanh::lean_box(0);
                            v_isShared_7790_ = v_isSharedCheck_7796_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_7563_);
                    v_a_7797_ = leanh::lean_ctor_get(v___x_7774_, 0);
                    v_isSharedCheck_7804_ = (!leanh::lean_is_exclusive(v___x_7774_)) as u8;
                    if v_isSharedCheck_7804_ == 0 {
                        v___x_7799_ = v___x_7774_;
                        v_isShared_7800_ = v_isSharedCheck_7804_;
                        state = 45;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7797_);
                        leanh::lean_dec(v___x_7774_);
                        v___x_7799_ = leanh::lean_box(0);
                        v_isShared_7800_ = v_isSharedCheck_7804_;
                        state = 45;
                        continue;
                    }
                }
            }
            41 => {
                v___x_7781_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_7782_ = (leanh::lean_unbox(v_a_7777_) as u8);
                leanh::lean_dec(v_a_7777_);
                leanh::lean_ctor_set_uint8(v___x_7781_, 0 as u32, v___x_7782_);
                if v_isShared_7780_ == 0 {
                    leanh::lean_ctor_set(v___x_7779_, 0, v___x_7781_);
                    v___x_7784_ = v___x_7779_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_7785_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7785_, 0, v___x_7781_);
                    v___x_7784_ = v_reuseFailAlloc_7785_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_7784_;
            }
            43 => {
                leanh::lean_inc(v_a_7787_);
                if v_isShared_7790_ == 0 {
                    v___x_7792_ = v___x_7789_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_7795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7795_, 0, v_a_7787_);
                    v___x_7792_ = v_reuseFailAlloc_7795_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_7793_ = l_Lean_Exception_isInterrupt(v_a_7787_);
                if v___x_7793_ == 0 {
                    v___x_7794_ = l_Lean_Exception_isRuntime(v_a_7787_);
                    v___y_7723_ = v___y_7772_;
                    v___y_7724_ = v___x_7792_;
                    v___y_7725_ = v_a_7775_;
                    v___y_7726_ = v___y_7773_;
                    v___y_7727_ = v___y_7771_;
                    v___y_7728_ = v___y_7770_;
                    v___y_7729_ = v___x_7794_;
                    state = 31;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7787_);
                    v___y_7723_ = v___y_7772_;
                    v___y_7724_ = v___x_7792_;
                    v___y_7725_ = v_a_7775_;
                    v___y_7726_ = v___y_7773_;
                    v___y_7727_ = v___y_7771_;
                    v___y_7728_ = v___y_7770_;
                    v___y_7729_ = v___x_7793_;
                    state = 31;
                    continue;
                }
            }
            45 => {
                if v_isShared_7800_ == 0 {
                    v___x_7802_ = v___x_7799_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_7803_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7803_, 0, v_a_7797_);
                    v___x_7802_ = v_reuseFailAlloc_7803_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_7802_;
            }
            47 => {
                v___x_7824_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_7825_ = (leanh::lean_unbox(v_a_7820_) as u8);
                leanh::lean_dec(v_a_7820_);
                leanh::lean_ctor_set_uint8(v___x_7824_, 0 as u32, v___x_7825_);
                if v_isShared_7823_ == 0 {
                    leanh::lean_ctor_set(v___x_7822_, 0, v___x_7824_);
                    v___x_7827_ = v___x_7822_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_7828_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7828_, 0, v___x_7824_);
                    v___x_7827_ = v_reuseFailAlloc_7828_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_7827_;
            }
            49 => {
                if v_isShared_7833_ == 0 {
                    v___x_7835_ = v___x_7832_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_7836_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7836_, 0, v_a_7830_);
                    v___x_7835_ = v_reuseFailAlloc_7836_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_7835_;
            }
            51 => {
                v___x_7843_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7843_, 0, v_a_7839_);
                if v_isShared_7842_ == 0 {
                    leanh::lean_ctor_set(v___x_7841_, 0, v___x_7843_);
                    v___x_7845_ = v___x_7841_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_7846_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7846_, 0, v___x_7843_);
                    v___x_7845_ = v_reuseFailAlloc_7846_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_7845_;
            }
            53 => {
                if v_isShared_7851_ == 0 {
                    v___x_7853_ = v___x_7850_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_7854_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7854_, 0, v_a_7848_);
                    v___x_7853_ = v_reuseFailAlloc_7854_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_7853_;
            }
            55 => {
                v___x_7861_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7861_, 0, v_a_7857_);
                if v_isShared_7860_ == 0 {
                    leanh::lean_ctor_set(v___x_7859_, 0, v___x_7861_);
                    v___x_7863_ = v___x_7859_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_7864_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7864_, 0, v___x_7861_);
                    v___x_7863_ = v_reuseFailAlloc_7864_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_7863_;
            }
            57 => {
                if v_isShared_7869_ == 0 {
                    v___x_7871_ = v___x_7868_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_7872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7872_, 0, v_a_7866_);
                    v___x_7871_ = v_reuseFailAlloc_7872_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_7871_;
            }
            59 => {
                v___x_7879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7879_, 0, v_a_7875_);
                if v_isShared_7878_ == 0 {
                    leanh::lean_ctor_set(v___x_7877_, 0, v___x_7879_);
                    v___x_7881_ = v___x_7877_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_7882_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7882_, 0, v___x_7879_);
                    v___x_7881_ = v_reuseFailAlloc_7882_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_7881_;
            }
            61 => {
                if v_isShared_7887_ == 0 {
                    v___x_7889_ = v___x_7886_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_7890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7890_, 0, v_a_7884_);
                    v___x_7889_ = v_reuseFailAlloc_7890_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_7889_;
            }
            63 => {
                v___x_7897_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7897_, 0, v_a_7893_);
                if v_isShared_7896_ == 0 {
                    leanh::lean_ctor_set(v___x_7895_, 0, v___x_7897_);
                    v___x_7899_ = v___x_7895_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_7900_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7900_, 0, v___x_7897_);
                    v___x_7899_ = v_reuseFailAlloc_7900_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_7899_;
            }
            65 => {
                if v_isShared_7905_ == 0 {
                    v___x_7907_ = v___x_7904_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_7908_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7908_, 0, v_a_7902_);
                    v___x_7907_ = v_reuseFailAlloc_7908_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                return v___x_7907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore___boxed(
    mut v_e_7910_: *mut leanh::LeanObject,
    mut v_a_7911_: *mut leanh::LeanObject,
    mut v_a_7912_: *mut leanh::LeanObject,
    mut v_a_7913_: *mut leanh::LeanObject,
    mut v_a_7914_: *mut leanh::LeanObject,
    mut v_a_7915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7916_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExprCore(
        v_e_7910_, v_a_7911_, v_a_7912_, v_a_7913_, v_a_7914_,
    );
    leanh::lean_dec(v_a_7914_);
    leanh::lean_dec_ref(v_a_7913_);
    leanh::lean_dec(v_a_7912_);
    leanh::lean_dec_ref(v_a_7911_);
    return v_res_7916_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7918_: u8 = 0;
    let mut v___x_7919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7918_ = 0;
    v___x_7919_ = l_Lean_Elab_ConfigEval_EvalTerm_instDataValue___closed__1;
    v___x_7920_ = l_Lean_MessageData_ofConstName(v___x_7919_, v___x_7918_);
    return v___x_7920_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7921_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__1,
    );
    v___x_7922_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__2,
    );
    v___x_7923_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7923_, 0, v___x_7922_);
    leanh::lean_ctor_set(v___x_7923_, 1, v___x_7921_);
    return v___x_7923_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7924_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr___closed__6,
    );
    v___x_7925_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__2,
    );
    v___x_7926_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7926_, 0, v___x_7925_);
    leanh::lean_ctor_set(v___x_7926_, 1, v___x_7924_);
    return v___x_7926_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(
    mut v_e_7927_: *mut leanh::LeanObject,
    mut v_a_7928_: *mut leanh::LeanObject,
    mut v_a_7929_: *mut leanh::LeanObject,
    mut v_a_7930_: *mut leanh::LeanObject,
    mut v_a_7931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7933_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__0;
    v___x_7934_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___closed__3,
    );
    v___x_7935_ = l_Lean_Elab_ConfigEval_EvalExpr_withWHNF___redArg(
        v___x_7933_,
        v_e_7927_,
        v___x_7934_,
        v_a_7928_,
        v_a_7929_,
        v_a_7930_,
        v_a_7931_,
    );
    return v___x_7935_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr___boxed(
    mut v_e_7936_: *mut leanh::LeanObject,
    mut v_a_7937_: *mut leanh::LeanObject,
    mut v_a_7938_: *mut leanh::LeanObject,
    mut v_a_7939_: *mut leanh::LeanObject,
    mut v_a_7940_: *mut leanh::LeanObject,
    mut v_a_7941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7942_ = l_Lean_Elab_ConfigEval_EvalExpr_evalDataValueExpr(
        v_e_7936_, v_a_7937_, v_a_7938_, v_a_7939_, v_a_7940_,
    );
    leanh::lean_dec(v_a_7940_);
    leanh::lean_dec_ref(v_a_7939_);
    leanh::lean_dec(v_a_7938_);
    leanh::lean_dec_ref(v_a_7937_);
    return v_res_7942_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7944_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalBoolStx___closed__3,
    );
    v___x_7945_ = l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__0;
    v___x_7946_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7946_, 0, v___x_7945_);
    leanh::lean_ctor_set(v___x_7946_, 1, v___x_7944_);
    return v___x_7946_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool() -> *mut leanh::LeanObject {
    let mut v___x_7947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7947_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool___closed__1,
    );
    return v___x_7947_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7949_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNatStx___closed__3,
    );
    v___x_7950_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__0;
    v___x_7951_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7951_, 0, v___x_7950_);
    leanh::lean_ctor_set(v___x_7951_, 1, v___x_7949_);
    return v___x_7951_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat() -> *mut leanh::LeanObject {
    let mut v___x_7952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7952_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat___closed__1,
    );
    return v___x_7952_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7954_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalIntStx___closed__3,
    );
    v___x_7955_ = l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__0;
    v___x_7956_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7956_, 0, v___x_7955_);
    leanh::lean_ctor_set(v___x_7956_, 1, v___x_7954_);
    return v___x_7956_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt() -> *mut leanh::LeanObject {
    let mut v___x_7957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7957_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt___closed__1,
    );
    return v___x_7957_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7959_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalStringStx___closed__3,
    );
    v___x_7960_ = l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__0;
    v___x_7961_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7961_, 0, v___x_7960_);
    leanh::lean_ctor_set(v___x_7961_, 1, v___x_7959_);
    return v___x_7961_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instString() -> *mut leanh::LeanObject {
    let mut v___x_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7962_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_instString___closed__1,
    );
    return v___x_7962_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7964_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3_once),
        _init_l_Lean_Elab_ConfigEval_EvalTerm_evalNameStx___closed__3,
    );
    v___x_7965_ = l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__0;
    v___x_7966_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7966_, 0, v___x_7965_);
    leanh::lean_ctor_set(v___x_7966_, 1, v___x_7964_);
    return v___x_7966_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_EvalExpr_instName() -> *mut leanh::LeanObject {
    let mut v___x_7967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7967_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1_once),
        _init_l_Lean_Elab_ConfigEval_EvalExpr_instName___closed__1,
    );
    return v___x_7967_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(
    mut v_inst_7968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalExpr_7969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_7970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7973_: u8 = 0;
    let mut v___x_7974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7981_: u8 = 0;
    let mut v___x_7982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7990_: u8 = 0;
    let mut v_isSharedCheck_7991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalExpr_7969_ = leanh::lean_ctor_get(v_inst_7968_, 0);
                v_expectedType_x3f_7970_ = leanh::lean_ctor_get(v_inst_7968_, 1);
                v_isSharedCheck_7991_ = (!leanh::lean_is_exclusive(v_inst_7968_)) as u8;
                if v_isSharedCheck_7991_ == 0 {
                    v___x_7972_ = v_inst_7968_;
                    v_isShared_7973_ = v_isSharedCheck_7991_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_expectedType_x3f_7970_);
                    leanh::lean_inc(v_evalExpr_7969_);
                    leanh::lean_dec(v_inst_7968_);
                    v___x_7972_ = leanh::lean_box(0);
                    v_isShared_7973_ = v_isSharedCheck_7991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7974_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalExpr_evalOptionExpr___boxed
                        as *mut core::ffi::c_void,
                    8,
                    2,
                );
                leanh::lean_closure_set(v___x_7974_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_7974_, 1, v_evalExpr_7969_);
                if leanh::lean_obj_tag(v_expectedType_x3f_7970_) == 0 {
                    if v_isShared_7973_ == 0 {
                        leanh::lean_ctor_set(v___x_7972_, 0, v___x_7974_);
                        v___x_7976_ = v___x_7972_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7977_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7977_, 0, v___x_7974_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_7977_,
                            1,
                            v_expectedType_x3f_7970_,
                        );
                        v___x_7976_ = v_reuseFailAlloc_7977_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_7978_ = leanh::lean_ctor_get(v_expectedType_x3f_7970_, 0);
                    v_isSharedCheck_7990_ =
                        (!leanh::lean_is_exclusive(v_expectedType_x3f_7970_)) as u8;
                    if v_isSharedCheck_7990_ == 0 {
                        v___x_7980_ = v_expectedType_x3f_7970_;
                        v_isShared_7981_ = v_isSharedCheck_7990_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7978_);
                        leanh::lean_dec(v_expectedType_x3f_7970_);
                        v___x_7980_ = leanh::lean_box(0);
                        v_isShared_7981_ = v_isSharedCheck_7990_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7976_;
            }
            3 => {
                v___x_7982_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalOptionStx___redArg___closed__2,
                );
                v___x_7983_ = l_Lean_Expr_app___override(v___x_7982_, v_val_7978_);
                if v_isShared_7981_ == 0 {
                    leanh::lean_ctor_set(v___x_7980_, 0, v___x_7983_);
                    v___x_7985_ = v___x_7980_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7989_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7989_, 0, v___x_7983_);
                    v___x_7985_ = v_reuseFailAlloc_7989_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7973_ == 0 {
                    leanh::lean_ctor_set(v___x_7972_, 1, v___x_7985_);
                    leanh::lean_ctor_set(v___x_7972_, 0, v___x_7974_);
                    v___x_7987_ = v___x_7972_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7988_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7988_, 0, v___x_7974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7988_, 1, v___x_7985_);
                    v___x_7987_ = v_reuseFailAlloc_7988_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instOption(
    mut v_00_u03b1_7992_: *mut leanh::LeanObject,
    mut v_inst_7993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7994_ = l_Lean_Elab_ConfigEval_EvalExpr_instOption___redArg(v_inst_7993_);
    return v___x_7994_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(
    mut v_evalExpr_7995_: *mut leanh::LeanObject,
    mut v_e_7996_: *mut leanh::LeanObject,
    mut v___y_7997_: *mut leanh::LeanObject,
    mut v___y_7998_: *mut leanh::LeanObject,
    mut v___y_7999_: *mut leanh::LeanObject,
    mut v___y_8000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8002_: u8 = 0;
    let mut v___x_8003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8002_ = 0;
    v___x_8003_ = l_Lean_Elab_ConfigEval_EvalExpr_evalListExpr___redArg(
        v_evalExpr_7995_,
        v_e_7996_,
        v___x_8002_,
        v___y_7997_,
        v___y_7998_,
        v___y_7999_,
        v___y_8000_,
    );
    return v___x_8003_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed(
    mut v_evalExpr_8004_: *mut leanh::LeanObject,
    mut v_e_8005_: *mut leanh::LeanObject,
    mut v___y_8006_: *mut leanh::LeanObject,
    mut v___y_8007_: *mut leanh::LeanObject,
    mut v___y_8008_: *mut leanh::LeanObject,
    mut v___y_8009_: *mut leanh::LeanObject,
    mut v___y_8010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8011_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0(
        v_evalExpr_8004_,
        v_e_8005_,
        v___y_8006_,
        v___y_8007_,
        v___y_8008_,
        v___y_8009_,
    );
    leanh::lean_dec(v___y_8009_);
    leanh::lean_dec_ref(v___y_8008_);
    leanh::lean_dec(v___y_8007_);
    leanh::lean_dec_ref(v___y_8006_);
    return v_res_8011_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(
    mut v_inst_8012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalExpr_8013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_8014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8017_: u8 = 0;
    let mut v___f_8018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8025_: u8 = 0;
    let mut v___x_8026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8034_: u8 = 0;
    let mut v_isSharedCheck_8035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalExpr_8013_ = leanh::lean_ctor_get(v_inst_8012_, 0);
                v_expectedType_x3f_8014_ = leanh::lean_ctor_get(v_inst_8012_, 1);
                v_isSharedCheck_8035_ = (!leanh::lean_is_exclusive(v_inst_8012_)) as u8;
                if v_isSharedCheck_8035_ == 0 {
                    v___x_8016_ = v_inst_8012_;
                    v_isShared_8017_ = v_isSharedCheck_8035_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_expectedType_x3f_8014_);
                    leanh::lean_inc(v_evalExpr_8013_);
                    leanh::lean_dec(v_inst_8012_);
                    v___x_8016_ = leanh::lean_box(0);
                    v_isShared_8017_ = v_isSharedCheck_8035_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_8018_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    7,
                    1,
                );
                leanh::lean_closure_set(v___f_8018_, 0, v_evalExpr_8013_);
                if leanh::lean_obj_tag(v_expectedType_x3f_8014_) == 0 {
                    if v_isShared_8017_ == 0 {
                        leanh::lean_ctor_set(v___x_8016_, 0, v___f_8018_);
                        v___x_8020_ = v___x_8016_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8021_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 0, v___f_8018_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_8021_,
                            1,
                            v_expectedType_x3f_8014_,
                        );
                        v___x_8020_ = v_reuseFailAlloc_8021_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_8022_ = leanh::lean_ctor_get(v_expectedType_x3f_8014_, 0);
                    v_isSharedCheck_8034_ =
                        (!leanh::lean_is_exclusive(v_expectedType_x3f_8014_)) as u8;
                    if v_isSharedCheck_8034_ == 0 {
                        v___x_8024_ = v_expectedType_x3f_8014_;
                        v_isShared_8025_ = v_isSharedCheck_8034_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8022_);
                        leanh::lean_dec(v_expectedType_x3f_8014_);
                        v___x_8024_ = leanh::lean_box(0);
                        v_isShared_8025_ = v_isSharedCheck_8034_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8020_;
            }
            3 => {
                v___x_8026_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalListStx___redArg___closed__1,
                );
                v___x_8027_ = l_Lean_Expr_app___override(v___x_8026_, v_val_8022_);
                if v_isShared_8025_ == 0 {
                    leanh::lean_ctor_set(v___x_8024_, 0, v___x_8027_);
                    v___x_8029_ = v___x_8024_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8033_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8033_, 0, v___x_8027_);
                    v___x_8029_ = v_reuseFailAlloc_8033_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_8017_ == 0 {
                    leanh::lean_ctor_set(v___x_8016_, 1, v___x_8029_);
                    leanh::lean_ctor_set(v___x_8016_, 0, v___f_8018_);
                    v___x_8031_ = v___x_8016_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8032_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8032_, 0, v___f_8018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8032_, 1, v___x_8029_);
                    v___x_8031_ = v_reuseFailAlloc_8032_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instList(
    mut v_00_u03b1_8036_: *mut leanh::LeanObject,
    mut v_inst_8037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8038_ = l_Lean_Elab_ConfigEval_EvalExpr_instList___redArg(v_inst_8037_);
    return v___x_8038_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(
    mut v_inst_8039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_evalExpr_8040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_8041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8044_: u8 = 0;
    let mut v___x_8045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8052_: u8 = 0;
    let mut v___x_8053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8061_: u8 = 0;
    let mut v_isSharedCheck_8062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_evalExpr_8040_ = leanh::lean_ctor_get(v_inst_8039_, 0);
                v_expectedType_x3f_8041_ = leanh::lean_ctor_get(v_inst_8039_, 1);
                v_isSharedCheck_8062_ = (!leanh::lean_is_exclusive(v_inst_8039_)) as u8;
                if v_isSharedCheck_8062_ == 0 {
                    v___x_8043_ = v_inst_8039_;
                    v_isShared_8044_ = v_isSharedCheck_8062_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_expectedType_x3f_8041_);
                    leanh::lean_inc(v_evalExpr_8040_);
                    leanh::lean_dec(v_inst_8039_);
                    v___x_8043_ = leanh::lean_box(0);
                    v_isShared_8044_ = v_isSharedCheck_8062_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8045_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_ConfigEval_EvalExpr_evalArrayExpr___boxed as *mut core::ffi::c_void,
                    8,
                    2,
                );
                leanh::lean_closure_set(v___x_8045_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_8045_, 1, v_evalExpr_8040_);
                if leanh::lean_obj_tag(v_expectedType_x3f_8041_) == 0 {
                    if v_isShared_8044_ == 0 {
                        leanh::lean_ctor_set(v___x_8043_, 0, v___x_8045_);
                        v___x_8047_ = v___x_8043_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8048_, 0, v___x_8045_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_8048_,
                            1,
                            v_expectedType_x3f_8041_,
                        );
                        v___x_8047_ = v_reuseFailAlloc_8048_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_8049_ = leanh::lean_ctor_get(v_expectedType_x3f_8041_, 0);
                    v_isSharedCheck_8061_ =
                        (!leanh::lean_is_exclusive(v_expectedType_x3f_8041_)) as u8;
                    if v_isSharedCheck_8061_ == 0 {
                        v___x_8051_ = v_expectedType_x3f_8041_;
                        v_isShared_8052_ = v_isSharedCheck_8061_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_8049_);
                        leanh::lean_dec(v_expectedType_x3f_8041_);
                        v___x_8051_ = leanh::lean_box(0);
                        v_isShared_8052_ = v_isSharedCheck_8061_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8047_;
            }
            3 => {
                v___x_8053_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2_once
                    ),
                    _init_l_Lean_Elab_ConfigEval_EvalTerm_evalArrayStx___redArg___closed__2,
                );
                v___x_8054_ = l_Lean_Expr_app___override(v___x_8053_, v_val_8049_);
                if v_isShared_8052_ == 0 {
                    leanh::lean_ctor_set(v___x_8051_, 0, v___x_8054_);
                    v___x_8056_ = v___x_8051_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8060_, 0, v___x_8054_);
                    v___x_8056_ = v_reuseFailAlloc_8060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_8044_ == 0 {
                    leanh::lean_ctor_set(v___x_8043_, 1, v___x_8056_);
                    leanh::lean_ctor_set(v___x_8043_, 0, v___x_8045_);
                    v___x_8058_ = v___x_8043_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8059_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8059_, 0, v___x_8045_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8059_, 1, v___x_8056_);
                    v___x_8058_ = v_reuseFailAlloc_8059_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_EvalExpr_instArray(
    mut v_00_u03b1_8063_: *mut leanh::LeanObject,
    mut v_inst_8064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8065_ = l_Lean_Elab_ConfigEval_EvalExpr_instArray___redArg(v_inst_8064_);
    return v___x_8065_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval_Instances(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_ConfigEval_EvalTerm_instBool = _init_l_Lean_Elab_ConfigEval_EvalTerm_instBool();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instBool);
    l_Lean_Elab_ConfigEval_EvalTerm_instNat = _init_l_Lean_Elab_ConfigEval_EvalTerm_instNat();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instNat);
    l_Lean_Elab_ConfigEval_EvalTerm_instInt = _init_l_Lean_Elab_ConfigEval_EvalTerm_instInt();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instInt);
    l_Lean_Elab_ConfigEval_EvalTerm_instString = _init_l_Lean_Elab_ConfigEval_EvalTerm_instString();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instString);
    l_Lean_Elab_ConfigEval_EvalTerm_instName = _init_l_Lean_Elab_ConfigEval_EvalTerm_instName();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instName);
    l_Lean_Elab_ConfigEval_EvalTerm_instDataValue =
        _init_l_Lean_Elab_ConfigEval_EvalTerm_instDataValue();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalTerm_instDataValue);
    l_Lean_Elab_ConfigEval_EvalExpr_instBool = _init_l_Lean_Elab_ConfigEval_EvalExpr_instBool();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instBool);
    l_Lean_Elab_ConfigEval_EvalExpr_instNat = _init_l_Lean_Elab_ConfigEval_EvalExpr_instNat();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instNat);
    l_Lean_Elab_ConfigEval_EvalExpr_instInt = _init_l_Lean_Elab_ConfigEval_EvalExpr_instInt();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instInt);
    l_Lean_Elab_ConfigEval_EvalExpr_instString = _init_l_Lean_Elab_ConfigEval_EvalExpr_instString();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instString);
    l_Lean_Elab_ConfigEval_EvalExpr_instName = _init_l_Lean_Elab_ConfigEval_EvalExpr_instName();
    leanh::lean_mark_persistent(l_Lean_Elab_ConfigEval_EvalExpr_instName);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval_Instances(
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
pub unsafe fn initialize_Lean_Elab_ConfigEval_Instances(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval_Instances(builtin);
}