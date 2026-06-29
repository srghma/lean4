// Lean compiler output
// Module: Lean.Elab.Tactic.Guard
// Imports: Init.Guard Lean.Elab.Command Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Guard::{initialize_Init_Guard, runtime_initialize_Init_Guard};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_liftTermElabM___redArg, l_Lean_Elab_Command_runTermElabM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainTarget___boxed, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_getLhs___boxed,
    runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    l_Lean_Elab_Tactic_elabTerm, l_Lean_Elab_Tactic_getFVarId,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_elabTermEnsuringType,
    l_Lean_Elab_Term_logUnassignedUsingErrorInfos, l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_consumeMData, l_Lean_Expr_hasMVar, l_Lean_mkConst};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_type, l_Lean_LocalDecl_value_x3f, lean_local_ctx_find,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_isExprDefEqGuarded, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Eval::l_Lean_Meta_evalExpr___redArg;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_get_size, lean_nat_dec_eq};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 108, 111, 110, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16701333901772390046 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 82, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11766820169793439539 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 68, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value)
            as *mut crate::leanh::LeanObject,
        4334716130055557871 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 83, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value)
            as *mut crate::leanh::LeanObject,
        16142497725452366017 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 108, 111, 110, 65, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value)
            as *mut crate::leanh::LeanObject,
        2800469225767172270 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [1 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 1,
    },
    m_objs: [2 as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 108, 111, 110, 69, 113, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3454211822294123381 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 82, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value)
            as *mut crate::leanh::LeanObject,
        4547212498149662503 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 68, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9469198591938552093 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 83, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value)
            as *mut crate::leanh::LeanObject,
        18100060585123032661 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 111, 108, 111, 110, 69, 113, 65, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value)
            as *mut crate::leanh::LeanObject,
        398647838421166144 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 113, 117, 97, 108, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17604351797772570779 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 82, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17078963301316888828 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 68, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9006235547594326259 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 83, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value)
            as *mut crate::leanh::LeanObject,
        13788227380297645704 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 117, 97, 108, 65, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value)
            as *mut crate::leanh::LeanObject,
        8682205543839346023 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        115, 121, 110, 116, 97, 99, 116, 105, 99, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108,
        32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1_value:
    crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 50,
    m_capacity: 50,
    m_length: 49,
    m_data: [
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97,
        108, 32, 40, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 97, 108, 108, 32, 99, 111,
        110, 115, 116, 97, 110, 116, 115, 41, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97,
        108, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3_value:
    crate::leanh::LeanStringObject<56> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 56,
    m_capacity: 56,
    m_length: 55,
    m_data: [
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97,
        108, 32, 40, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 114, 101, 100, 117, 99, 105,
        98, 108, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 41, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4_value:
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
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97,
        108, 32, 40, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 105, 110, 115, 116, 97, 110,
        99, 101, 115, 41, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5_value:
    crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97,
        108, 32, 40, 110, 111, 116, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 97, 110,
        121, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 41, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        97, 108, 112, 104, 97, 45, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0_value:
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
    m_data: [70, 97, 105, 108, 101, 100, 58, 32, 96, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2_value:
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
    m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4_value:
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
    m_data: [32, 96, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value:
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
    m_data: [103, 117, 97, 114, 100, 69, 120, 112, 114, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        2406710036554907729 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        103, 117, 97, 114, 100, 69, 120, 112, 114, 67, 111, 110, 118, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value)
            as *mut crate::leanh::LeanObject,
        17520459286155217955 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [71, 117, 97, 114, 100, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value) as *mut crate::leanh::LeanObject,58792184315864126 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 75 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 82 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 75 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 75 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 17 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 69, 120, 112, 114, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value) as *mut crate::leanh::LeanObject,2900613087037517015 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 21 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        84, 104, 101, 32, 109, 97, 105, 110, 32, 103, 111, 97, 108, 32, 105, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        10, 98, 117, 116, 32, 119, 97, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116,
        111, 32, 98, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [103, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9705855369448785090 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        103, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 67, 111, 110, 118, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value)
            as *mut crate::leanh::LeanObject,
        1133233218418288393 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4_value:
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
    m_fun: l_Lean_Elab_Tactic_Conv_getLhs___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5_value:
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
    m_fun: l_Lean_Elab_Tactic_getMainTarget___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value) as *mut crate::leanh::LeanObject,13924985917103118701 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 99 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value) as *mut crate::leanh::LeanObject,3277492080379021737 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 23 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 108, 101, 116, 32, 98, 105, 110, 100, 105,
        110, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2_value:
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
        96, 32, 105, 115, 32, 97, 32, 108, 101, 116, 32, 98, 105, 110, 100, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [72, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 96, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [96, 32, 104, 97, 115, 32, 118, 97, 108, 117, 101, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        10, 98, 117, 116, 32, 119, 97, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116,
        111, 32, 104, 97, 118, 101, 32, 118, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [96, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        10, 98, 117, 116, 32, 119, 97, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116,
        111, 32, 104, 97, 118, 101, 32, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [96, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 117, 97, 114, 100, 72, 121, 112, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12801252452760768259 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [103, 117, 97, 114, 100, 72, 121, 112, 67, 111, 110, 118, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value)
            as *mut crate::leanh::LeanObject,
        9950005495765075193 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 72, 121, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value) as *mut crate::leanh::LeanObject,10552425012879073248 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 106 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 130 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 106 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 106 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 72, 121, 112, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value) as *mut crate::leanh::LeanObject,283289726733858414 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 45 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [103, 117, 97, 114, 100, 69, 120, 112, 114, 67, 109, 100, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        2836449611787596701 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 69, 120, 112, 114, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value) as *mut crate::leanh::LeanObject,14034849119720398400 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 136 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 143 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 136 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 136 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 20 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value) as *mut crate::leanh::LeanObject,12882480457794858234 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        10, 100, 105, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116,
        111, 32, 96, 116, 114, 117, 101, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [103, 117, 97, 114, 100, 67, 109, 100, 0],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8409249086422357623 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut crate::leanh::LeanObject,9301301477787065558 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value) as *mut crate::leanh::LeanObject,17344053803254828559 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 146 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 158 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 146 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 146 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx(
    mut v_x_2484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2484_) {
        0 => {
            let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2485_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2485_;
        }
        1 => {
            let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2486_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2486_;
        }
        _ => {
            let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2487_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2487_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___boxed(
    mut v_x_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2489_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx(v_x_2488_);
    crate::leanh::lean_dec(v_x_2488_);
    return v_res_2489_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(
    mut v_t_2490_: *mut crate::leanh::LeanObject,
    mut v_k_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2490_) == 1 {
        let mut v_red_2492_: u8 = 0;
        let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_red_2492_ = crate::leanh::lean_ctor_get_uint8(v_t_2490_, 0 as u32);
        v___x_2493_ = crate::leanh::lean_box((v_red_2492_) as usize);
        v___x_2494_ = crate::leanh::lean_apply_1(v_k_2491_, v___x_2493_);
        return v___x_2494_;
    } else {
        return v_k_2491_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg___boxed(
    mut v_t_2495_: *mut crate::leanh::LeanObject,
    mut v_k_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2497_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2495_, v_k_2496_);
    crate::leanh::lean_dec(v_t_2495_);
    return v_res_2497_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(
    mut v_motive_2498_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2499_: *mut crate::leanh::LeanObject,
    mut v_t_2500_: *mut crate::leanh::LeanObject,
    mut v_h_2501_: *mut crate::leanh::LeanObject,
    mut v_k_2502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2503_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2500_, v_k_2502_);
    return v___x_2503_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___boxed(
    mut v_motive_2504_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2505_: *mut crate::leanh::LeanObject,
    mut v_t_2506_: *mut crate::leanh::LeanObject,
    mut v_h_2507_: *mut crate::leanh::LeanObject,
    mut v_k_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(
        v_motive_2504_,
        v_ctorIdx_2505_,
        v_t_2506_,
        v_h_2507_,
        v_k_2508_,
    );
    crate::leanh::lean_dec(v_t_2506_);
    crate::leanh::lean_dec(v_ctorIdx_2505_);
    return v_res_2509_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(
    mut v_t_2510_: *mut crate::leanh::LeanObject,
    mut v_syntactic_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2512_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2510_, v_syntactic_2511_);
    return v___x_2512_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg___boxed(
    mut v_t_2513_: *mut crate::leanh::LeanObject,
    mut v_syntactic_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(
        v_t_2513_,
        v_syntactic_2514_,
    );
    crate::leanh::lean_dec(v_t_2513_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(
    mut v_motive_2516_: *mut crate::leanh::LeanObject,
    mut v_t_2517_: *mut crate::leanh::LeanObject,
    mut v_h_2518_: *mut crate::leanh::LeanObject,
    mut v_syntactic_2519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2520_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2517_, v_syntactic_2519_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___boxed(
    mut v_motive_2521_: *mut crate::leanh::LeanObject,
    mut v_t_2522_: *mut crate::leanh::LeanObject,
    mut v_h_2523_: *mut crate::leanh::LeanObject,
    mut v_syntactic_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(
        v_motive_2521_,
        v_t_2522_,
        v_h_2523_,
        v_syntactic_2524_,
    );
    crate::leanh::lean_dec(v_t_2522_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(
    mut v_t_2526_: *mut crate::leanh::LeanObject,
    mut v_defEq_2527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2528_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2526_, v_defEq_2527_);
    return v___x_2528_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg___boxed(
    mut v_t_2529_: *mut crate::leanh::LeanObject,
    mut v_defEq_2530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2531_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(v_t_2529_, v_defEq_2530_);
    crate::leanh::lean_dec(v_t_2529_);
    return v_res_2531_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(
    mut v_motive_2532_: *mut crate::leanh::LeanObject,
    mut v_t_2533_: *mut crate::leanh::LeanObject,
    mut v_h_2534_: *mut crate::leanh::LeanObject,
    mut v_defEq_2535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2536_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2533_, v_defEq_2535_);
    return v___x_2536_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___boxed(
    mut v_motive_2537_: *mut crate::leanh::LeanObject,
    mut v_t_2538_: *mut crate::leanh::LeanObject,
    mut v_h_2539_: *mut crate::leanh::LeanObject,
    mut v_defEq_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2541_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(
        v_motive_2537_,
        v_t_2538_,
        v_h_2539_,
        v_defEq_2540_,
    );
    crate::leanh::lean_dec(v_t_2538_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(
    mut v_t_2542_: *mut crate::leanh::LeanObject,
    mut v_alphaEq_2543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2542_, v_alphaEq_2543_);
    return v___x_2544_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg___boxed(
    mut v_t_2545_: *mut crate::leanh::LeanObject,
    mut v_alphaEq_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2547_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(v_t_2545_, v_alphaEq_2546_);
    crate::leanh::lean_dec(v_t_2545_);
    return v_res_2547_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(
    mut v_motive_2548_: *mut crate::leanh::LeanObject,
    mut v_t_2549_: *mut crate::leanh::LeanObject,
    mut v_h_2550_: *mut crate::leanh::LeanObject,
    mut v_alphaEq_2551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2549_, v_alphaEq_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___boxed(
    mut v_motive_2553_: *mut crate::leanh::LeanObject,
    mut v_t_2554_: *mut crate::leanh::LeanObject,
    mut v_h_2555_: *mut crate::leanh::LeanObject,
    mut v_alphaEq_2556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(
        v_motive_2553_,
        v_t_2554_,
        v_h_2555_,
        v_alphaEq_2556_,
    );
    crate::leanh::lean_dec(v_t_2554_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(
    mut v_x_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    v___x_2598_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3;
    crate::leanh::lean_inc(v_x_2597_);
    v___x_2599_ = l_Lean_Syntax_isOfKind(v_x_2597_, v___x_2598_);
    if v___x_2599_ == 0 {
        let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2597_);
        v___x_2600_ = crate::leanh::lean_box(0);
        return v___x_2600_;
    } else {
        let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2604_: u8 = 0;
        v___x_2601_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2602_ = l_Lean_Syntax_getArg(v_x_2597_, v___x_2601_);
        crate::leanh::lean_dec(v_x_2597_);
        v___x_2603_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5;
        crate::leanh::lean_inc(v___x_2602_);
        v___x_2604_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2603_);
        if v___x_2604_ == 0 {
            let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2606_: u8 = 0;
            v___x_2605_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7;
            crate::leanh::lean_inc(v___x_2602_);
            v___x_2606_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2605_);
            if v___x_2606_ == 0 {
                let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2608_: u8 = 0;
                v___x_2607_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9;
                crate::leanh::lean_inc(v___x_2602_);
                v___x_2608_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2607_);
                if v___x_2608_ == 0 {
                    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2610_: u8 = 0;
                    v___x_2609_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11;
                    v___x_2610_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2609_);
                    if v___x_2610_ == 0 {
                        let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2611_ = crate::leanh::lean_box(0);
                        return v___x_2611_;
                    } else {
                        let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2612_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
                        return v___x_2612_;
                    }
                } else {
                    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_2602_);
                    v___x_2613_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
                    return v___x_2613_;
                }
            } else {
                let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2602_);
                v___x_2614_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
                return v___x_2614_;
            }
        } else {
            let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2602_);
            v___x_2615_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
            return v___x_2615_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(
    mut v_x_2641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    v___x_2642_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1;
    crate::leanh::lean_inc(v_x_2641_);
    v___x_2643_ = l_Lean_Syntax_isOfKind(v_x_2641_, v___x_2642_);
    if v___x_2643_ == 0 {
        let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2641_);
        v___x_2644_ = crate::leanh::lean_box(0);
        return v___x_2644_;
    } else {
        let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: u8 = 0;
        v___x_2645_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2646_ = l_Lean_Syntax_getArg(v_x_2641_, v___x_2645_);
        crate::leanh::lean_dec(v_x_2641_);
        v___x_2647_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3;
        crate::leanh::lean_inc(v___x_2646_);
        v___x_2648_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2647_);
        if v___x_2648_ == 0 {
            let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2650_: u8 = 0;
            v___x_2649_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5;
            crate::leanh::lean_inc(v___x_2646_);
            v___x_2650_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2649_);
            if v___x_2650_ == 0 {
                let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2652_: u8 = 0;
                v___x_2651_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7;
                crate::leanh::lean_inc(v___x_2646_);
                v___x_2652_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2651_);
                if v___x_2652_ == 0 {
                    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2654_: u8 = 0;
                    v___x_2653_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9;
                    v___x_2654_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2653_);
                    if v___x_2654_ == 0 {
                        let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2655_ = crate::leanh::lean_box(0);
                        return v___x_2655_;
                    } else {
                        let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2656_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
                        return v___x_2656_;
                    }
                } else {
                    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_2646_);
                    v___x_2657_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
                    return v___x_2657_;
                }
            } else {
                let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2646_);
                v___x_2658_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
                return v___x_2658_;
            }
        } else {
            let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2646_);
            v___x_2659_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
            return v___x_2659_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(
    mut v_x_2685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    v___x_2686_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
    crate::leanh::lean_inc(v_x_2685_);
    v___x_2687_ = l_Lean_Syntax_isOfKind(v_x_2685_, v___x_2686_);
    if v___x_2687_ == 0 {
        let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_2685_);
        v___x_2688_ = crate::leanh::lean_box(0);
        return v___x_2688_;
    } else {
        let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2692_: u8 = 0;
        v___x_2689_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2690_ = l_Lean_Syntax_getArg(v_x_2685_, v___x_2689_);
        crate::leanh::lean_dec(v_x_2685_);
        v___x_2691_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3;
        crate::leanh::lean_inc(v___x_2690_);
        v___x_2692_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2691_);
        if v___x_2692_ == 0 {
            let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2694_: u8 = 0;
            v___x_2693_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5;
            crate::leanh::lean_inc(v___x_2690_);
            v___x_2694_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2693_);
            if v___x_2694_ == 0 {
                let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2696_: u8 = 0;
                v___x_2695_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7;
                crate::leanh::lean_inc(v___x_2690_);
                v___x_2696_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2695_);
                if v___x_2696_ == 0 {
                    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_2698_: u8 = 0;
                    v___x_2697_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9;
                    v___x_2698_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2697_);
                    if v___x_2698_ == 0 {
                        let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2699_ = crate::leanh::lean_box(0);
                        return v___x_2699_;
                    } else {
                        let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_2700_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
                        return v___x_2700_;
                    }
                } else {
                    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v___x_2690_);
                    v___x_2701_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
                    return v___x_2701_;
                }
            } else {
                let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_2690_);
                v___x_2702_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
                return v___x_2702_;
            }
        } else {
            let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_2690_);
            v___x_2703_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
            return v___x_2703_;
        }
    }
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(
    mut v_x_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut v_unused_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_a_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut v_unused_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_a_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2710_ = l_Lean_Meta_saveState___redArg(v___y_2706_, v___y_2708_);
                if crate::leanh::lean_obj_tag(v___x_2710_) == 0 {
                    v_a_2711_ = crate::leanh::lean_ctor_get(v___x_2710_, 0);
                    crate::leanh::lean_inc(v_a_2711_);
                    crate::leanh::lean_dec_ref_known(v___x_2710_, 1);
                    crate::leanh::lean_inc(v___y_2708_);
                    crate::leanh::lean_inc_ref(v___y_2707_);
                    crate::leanh::lean_inc(v___y_2706_);
                    crate::leanh::lean_inc_ref(v___y_2705_);
                    v_r_2712_ = crate::leanh::lean_apply_5(
                        v_x_2704_,
                        v___y_2705_,
                        v___y_2706_,
                        v___y_2707_,
                        v___y_2708_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_2712_) == 0 {
                        v_a_2713_ = crate::leanh::lean_ctor_get(v_r_2712_, 0);
                        crate::leanh::lean_inc(v_a_2713_);
                        crate::leanh::lean_dec_ref_known(v_r_2712_, 1);
                        v___x_2714_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_2711_,
                            v___y_2706_,
                            v___y_2708_,
                        );
                        crate::leanh::lean_dec(v_a_2711_);
                        if crate::leanh::lean_obj_tag(v___x_2714_) == 0 {
                            v_isSharedCheck_2721_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2714_)) as u8;
                            if v_isSharedCheck_2721_ == 0 {
                                v_unused_2722_ = crate::leanh::lean_ctor_get(v___x_2714_, 0);
                                crate::leanh::lean_dec(v_unused_2722_);
                                v___x_2716_ = v___x_2714_;
                                v_isShared_2717_ = v_isSharedCheck_2721_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2714_);
                                v___x_2716_ = crate::leanh::lean_box(0);
                                v_isShared_2717_ = v_isSharedCheck_2721_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2713_);
                            v_a_2723_ = crate::leanh::lean_ctor_get(v___x_2714_, 0);
                            v_isSharedCheck_2730_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2714_)) as u8;
                            if v_isSharedCheck_2730_ == 0 {
                                v___x_2725_ = v___x_2714_;
                                v_isShared_2726_ = v_isSharedCheck_2730_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2723_);
                                crate::leanh::lean_dec(v___x_2714_);
                                v___x_2725_ = crate::leanh::lean_box(0);
                                v_isShared_2726_ = v_isSharedCheck_2730_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_2731_ = crate::leanh::lean_ctor_get(v_r_2712_, 0);
                        crate::leanh::lean_inc(v_a_2731_);
                        crate::leanh::lean_dec_ref_known(v_r_2712_, 1);
                        v___x_2732_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_2711_,
                            v___y_2706_,
                            v___y_2708_,
                        );
                        crate::leanh::lean_dec(v_a_2711_);
                        if crate::leanh::lean_obj_tag(v___x_2732_) == 0 {
                            v_isSharedCheck_2739_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2732_)) as u8;
                            if v_isSharedCheck_2739_ == 0 {
                                v_unused_2740_ = crate::leanh::lean_ctor_get(v___x_2732_, 0);
                                crate::leanh::lean_dec(v_unused_2740_);
                                v___x_2734_ = v___x_2732_;
                                v_isShared_2735_ = v_isSharedCheck_2739_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2732_);
                                v___x_2734_ = crate::leanh::lean_box(0);
                                v_isShared_2735_ = v_isSharedCheck_2739_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2731_);
                            v_a_2741_ = crate::leanh::lean_ctor_get(v___x_2732_, 0);
                            v_isSharedCheck_2748_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2732_)) as u8;
                            if v_isSharedCheck_2748_ == 0 {
                                v___x_2743_ = v___x_2732_;
                                v_isShared_2744_ = v_isSharedCheck_2748_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2741_);
                                crate::leanh::lean_dec(v___x_2732_);
                                v___x_2743_ = crate::leanh::lean_box(0);
                                v_isShared_2744_ = v_isSharedCheck_2748_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_2704_);
                    v_a_2749_ = crate::leanh::lean_ctor_get(v___x_2710_, 0);
                    v_isSharedCheck_2756_ = (!crate::leanh::lean_is_exclusive(v___x_2710_)) as u8;
                    if v_isSharedCheck_2756_ == 0 {
                        v___x_2751_ = v___x_2710_;
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2749_);
                        crate::leanh::lean_dec(v___x_2710_);
                        v___x_2751_ = crate::leanh::lean_box(0);
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2716_, 0, v_a_2713_);
                    v___x_2719_ = v___x_2716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2713_);
                    v___x_2719_ = v_reuseFailAlloc_2720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2719_;
            }
            3 => {
                if v_isShared_2726_ == 0 {
                    v___x_2728_ = v___x_2725_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2729_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
                    v___x_2728_ = v_reuseFailAlloc_2729_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2728_;
            }
            5 => {
                if v_isShared_2735_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2734_, 1);
                    crate::leanh::lean_ctor_set(v___x_2734_, 0, v_a_2731_);
                    v___x_2737_ = v___x_2734_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2731_);
                    v___x_2737_ = v_reuseFailAlloc_2738_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2737_;
            }
            7 => {
                if v_isShared_2744_ == 0 {
                    v___x_2746_ = v___x_2743_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
                    v___x_2746_ = v_reuseFailAlloc_2747_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2746_;
            }
            9 => {
                if v_isShared_2752_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg___boxed(
    mut v_x_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2763_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
    crate::leanh::lean_dec(v___y_2761_);
    crate::leanh::lean_dec_ref(v___y_2760_);
    crate::leanh::lean_dec(v___y_2759_);
    crate::leanh::lean_dec_ref(v___y_2758_);
    return v_res_2763_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(
    mut v_00_u03b1_2764_: *mut crate::leanh::LeanObject,
    mut v_x_2765_: *mut crate::leanh::LeanObject,
    mut v___y_2766_: *mut crate::leanh::LeanObject,
    mut v___y_2767_: *mut crate::leanh::LeanObject,
    mut v___y_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2771_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
    return v___x_2771_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___boxed(
    mut v_00_u03b1_2772_: *mut crate::leanh::LeanObject,
    mut v_x_2773_: *mut crate::leanh::LeanObject,
    mut v___y_2774_: *mut crate::leanh::LeanObject,
    mut v___y_2775_: *mut crate::leanh::LeanObject,
    mut v___y_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2779_ =
        l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(
            v_00_u03b1_2772_,
            v_x_2773_,
            v___y_2774_,
            v___y_2775_,
            v___y_2776_,
            v___y_2777_,
        );
    crate::leanh::lean_dec(v___y_2777_);
    crate::leanh::lean_dec_ref(v___y_2776_);
    crate::leanh::lean_dec(v___y_2775_);
    crate::leanh::lean_dec_ref(v___y_2774_);
    return v_res_2779_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(
    mut v_red_2780_: u8,
    mut v_a_2781_: *mut crate::leanh::LeanObject,
    mut v_b_2782_: *mut crate::leanh::LeanObject,
    mut v___y_2783_: *mut crate::leanh::LeanObject,
    mut v___y_2784_: *mut crate::leanh::LeanObject,
    mut v___y_2785_: *mut crate::leanh::LeanObject,
    mut v___y_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2789_: u8 = 0;
    let mut v_ctxApprox_2790_: u8 = 0;
    let mut v_quasiPatternApprox_2791_: u8 = 0;
    let mut v_constApprox_2792_: u8 = 0;
    let mut v_isDefEqStuckEx_2793_: u8 = 0;
    let mut v_unificationHints_2794_: u8 = 0;
    let mut v_proofIrrelevance_2795_: u8 = 0;
    let mut v_assignSyntheticOpaque_2796_: u8 = 0;
    let mut v_offsetCnstrs_2797_: u8 = 0;
    let mut v_etaStruct_2798_: u8 = 0;
    let mut v_univApprox_2799_: u8 = 0;
    let mut v_iota_2800_: u8 = 0;
    let mut v_beta_2801_: u8 = 0;
    let mut v_proj_2802_: u8 = 0;
    let mut v_zeta_2803_: u8 = 0;
    let mut v_zetaDelta_2804_: u8 = 0;
    let mut v_zetaUnused_2805_: u8 = 0;
    let mut v_zetaHave_2806_: u8 = 0;
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2809_: u8 = 0;
    let mut v_trackZetaDelta_2810_: u8 = 0;
    let mut v_zetaDeltaSet_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2817_: u8 = 0;
    let mut v_inTypeClassResolution_2818_: u8 = 0;
    let mut v_cacheInferType_2819_: u8 = 0;
    let mut v_config_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u64 = 0;
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: u64 = 0;
    let mut v___x_2827_: u64 = 0;
    let mut v___x_2828_: u64 = 0;
    let mut v___x_2829_: u64 = 0;
    let mut v_key_2830_: u64 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut v_unused_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2788_ = l_Lean_Meta_Context_config(v___y_2783_);
                v_foApprox_2789_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 0 as u32);
                v_ctxApprox_2790_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 1 as u32);
                v_quasiPatternApprox_2791_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2788_, 2 as u32);
                v_constApprox_2792_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 3 as u32);
                v_isDefEqStuckEx_2793_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 4 as u32);
                v_unificationHints_2794_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 5 as u32);
                v_proofIrrelevance_2795_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 6 as u32);
                v_assignSyntheticOpaque_2796_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2788_, 7 as u32);
                v_offsetCnstrs_2797_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 8 as u32);
                v_etaStruct_2798_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 10 as u32);
                v_univApprox_2799_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 11 as u32);
                v_iota_2800_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 12 as u32);
                v_beta_2801_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 13 as u32);
                v_proj_2802_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 14 as u32);
                v_zeta_2803_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 15 as u32);
                v_zetaDelta_2804_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 16 as u32);
                v_zetaUnused_2805_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 17 as u32);
                v_zetaHave_2806_ = crate::leanh::lean_ctor_get_uint8(v___x_2788_, 18 as u32);
                v_isSharedCheck_2845_ = (!crate::leanh::lean_is_exclusive(v___x_2788_)) as u8;
                if v_isSharedCheck_2845_ == 0 {
                    v___x_2808_ = v___x_2788_;
                    v_isShared_2809_ = v_isSharedCheck_2845_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2788_);
                    v___x_2808_ = crate::leanh::lean_box(0);
                    v_isShared_2809_ = v_isSharedCheck_2845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_2810_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2811_ = crate::leanh::lean_ctor_get(v___y_2783_, 1);
                crate::leanh::lean_inc(v_zetaDeltaSet_2811_);
                v_lctx_2812_ = crate::leanh::lean_ctor_get(v___y_2783_, 2);
                crate::leanh::lean_inc_ref(v_lctx_2812_);
                v_localInstances_2813_ = crate::leanh::lean_ctor_get(v___y_2783_, 3);
                crate::leanh::lean_inc_ref(v_localInstances_2813_);
                v_defEqCtx_x3f_2814_ = crate::leanh::lean_ctor_get(v___y_2783_, 4);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2814_);
                v_synthPendingDepth_2815_ = crate::leanh::lean_ctor_get(v___y_2783_, 5);
                crate::leanh::lean_inc(v_synthPendingDepth_2815_);
                v_canUnfold_x3f_2816_ = crate::leanh::lean_ctor_get(v___y_2783_, 6);
                crate::leanh::lean_inc(v_canUnfold_x3f_2816_);
                v_univApprox_2817_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2818_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2819_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2809_ == 0 {
                    v_config_2821_ = v___x_2808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2844_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        0 as u32,
                        v_foApprox_2789_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        1 as u32,
                        v_ctxApprox_2790_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        2 as u32,
                        v_quasiPatternApprox_2791_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        3 as u32,
                        v_constApprox_2792_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        4 as u32,
                        v_isDefEqStuckEx_2793_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        5 as u32,
                        v_unificationHints_2794_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        6 as u32,
                        v_proofIrrelevance_2795_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        7 as u32,
                        v_assignSyntheticOpaque_2796_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        8 as u32,
                        v_offsetCnstrs_2797_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        10 as u32,
                        v_etaStruct_2798_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        11 as u32,
                        v_univApprox_2799_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        12 as u32,
                        v_iota_2800_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        13 as u32,
                        v_beta_2801_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        14 as u32,
                        v_proj_2802_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        15 as u32,
                        v_zeta_2803_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        16 as u32,
                        v_zetaDelta_2804_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        17 as u32,
                        v_zetaUnused_2805_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        18 as u32,
                        v_zetaHave_2806_,
                    );
                    v_config_2821_ = v_reuseFailAlloc_2844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2821_, 9 as u32, v_red_2780_);
                v___x_2822_ = l_Lean_Meta_Context_configKey(v___y_2783_);
                v_isSharedCheck_2836_ = (!crate::leanh::lean_is_exclusive(v___y_2783_)) as u8;
                if v_isSharedCheck_2836_ == 0 {
                    v_unused_2837_ = crate::leanh::lean_ctor_get(v___y_2783_, 6);
                    crate::leanh::lean_dec(v_unused_2837_);
                    v_unused_2838_ = crate::leanh::lean_ctor_get(v___y_2783_, 5);
                    crate::leanh::lean_dec(v_unused_2838_);
                    v_unused_2839_ = crate::leanh::lean_ctor_get(v___y_2783_, 4);
                    crate::leanh::lean_dec(v_unused_2839_);
                    v_unused_2840_ = crate::leanh::lean_ctor_get(v___y_2783_, 3);
                    crate::leanh::lean_dec(v_unused_2840_);
                    v_unused_2841_ = crate::leanh::lean_ctor_get(v___y_2783_, 2);
                    crate::leanh::lean_dec(v_unused_2841_);
                    v_unused_2842_ = crate::leanh::lean_ctor_get(v___y_2783_, 1);
                    crate::leanh::lean_dec(v_unused_2842_);
                    v_unused_2843_ = crate::leanh::lean_ctor_get(v___y_2783_, 0);
                    crate::leanh::lean_dec(v_unused_2843_);
                    v___x_2824_ = v___y_2783_;
                    v_isShared_2825_ = v_isSharedCheck_2836_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2783_);
                    v___x_2824_ = crate::leanh::lean_box(0);
                    v_isShared_2825_ = v_isSharedCheck_2836_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2826_ = 3u64;
                v___x_2827_ = lean_uint64_shift_right(v___x_2822_, v___x_2826_);
                v___x_2828_ = lean_uint64_shift_left(v___x_2827_, v___x_2826_);
                v___x_2829_ = l_Lean_Meta_TransparencyMode_toUInt64(v_red_2780_);
                v_key_2830_ = lean_uint64_lor(v___x_2828_, v___x_2829_);
                v___x_2831_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2831_, 0, v_config_2821_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2831_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2830_,
                );
                if v_isShared_2825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2824_, 0, v___x_2831_);
                    v___x_2833_ = v___x_2824_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_zetaDeltaSet_2811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_lctx_2812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 3, v_localInstances_2813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 4, v_defEqCtx_x3f_2814_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2835_,
                        5,
                        v_synthPendingDepth_2815_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2835_, 6, v_canUnfold_x3f_2816_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_trackZetaDelta_2810_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                        v_univApprox_2817_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_2818_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_2819_,
                    );
                    v___x_2833_ = v_reuseFailAlloc_2835_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2834_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_a_2781_,
                    v_b_2782_,
                    v___x_2833_,
                    v___y_2784_,
                    v___y_2785_,
                    v___y_2786_,
                );
                crate::leanh::lean_dec_ref(v___x_2833_);
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(
    mut v_red_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
    mut v_b_2848_: *mut crate::leanh::LeanObject,
    mut v___y_2849_: *mut crate::leanh::LeanObject,
    mut v___y_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
    mut v___y_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_red_1788__boxed_2854_: u8 = 0;
    let mut v_res_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_red_1788__boxed_2854_ = (crate::leanh::lean_unbox(v_red_2846_) as u8);
    v_res_2855_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(
        v_red_1788__boxed_2854_,
        v_a_2847_,
        v_b_2848_,
        v___y_2849_,
        v___y_2850_,
        v___y_2851_,
        v___y_2852_,
    );
    crate::leanh::lean_dec(v___y_2852_);
    crate::leanh::lean_dec_ref(v___y_2851_);
    crate::leanh::lean_dec(v___y_2850_);
    return v_res_2855_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
    mut v_a_2856_: *mut crate::leanh::LeanObject,
    mut v_b_2857_: *mut crate::leanh::LeanObject,
    mut v_x_2858_: *mut crate::leanh::LeanObject,
    mut v_a_2859_: *mut crate::leanh::LeanObject,
    mut v_a_2860_: *mut crate::leanh::LeanObject,
    mut v_a_2861_: *mut crate::leanh::LeanObject,
    mut v_a_2862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2858_) {
        0 => {
            let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2866_: u8 = 0;
            let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2864_ = l_Lean_Expr_consumeMData(v_a_2856_);
            crate::leanh::lean_dec_ref(v_a_2856_);
            v___x_2865_ = l_Lean_Expr_consumeMData(v_b_2857_);
            crate::leanh::lean_dec_ref(v_b_2857_);
            v___x_2866_ = lean_expr_eqv(v___x_2864_, v___x_2865_);
            crate::leanh::lean_dec_ref(v___x_2865_);
            crate::leanh::lean_dec_ref(v___x_2864_);
            v___x_2867_ = crate::leanh::lean_box((v___x_2866_) as usize);
            v___x_2868_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2867_);
            return v___x_2868_;
        }
        1 => {
            let mut v_red_2869_: u8 = 0;
            let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_red_2869_ = crate::leanh::lean_ctor_get_uint8(v_x_2858_, 0 as u32);
            v___x_2870_ = crate::leanh::lean_box((v_red_2869_) as usize);
            v___f_2871_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed
                    as *mut core::ffi::c_void,
                8,
                3,
            );
            crate::leanh::lean_closure_set(v___f_2871_, 0, v___x_2870_);
            crate::leanh::lean_closure_set(v___f_2871_, 1, v_a_2856_);
            crate::leanh::lean_closure_set(v___f_2871_, 2, v_b_2857_);
            v___x_2872_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v___f_2871_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
            return v___x_2872_;
        }
        _ => {
            let mut v___x_2873_: u8 = 0;
            let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2873_ = lean_expr_eqv(v_a_2856_, v_b_2857_);
            crate::leanh::lean_dec_ref(v_b_2857_);
            crate::leanh::lean_dec_ref(v_a_2856_);
            v___x_2874_ = crate::leanh::lean_box((v___x_2873_) as usize);
            v___x_2875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2875_, 0, v___x_2874_);
            return v___x_2875_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(
    mut v_a_2876_: *mut crate::leanh::LeanObject,
    mut v_b_2877_: *mut crate::leanh::LeanObject,
    mut v_x_2878_: *mut crate::leanh::LeanObject,
    mut v_a_2879_: *mut crate::leanh::LeanObject,
    mut v_a_2880_: *mut crate::leanh::LeanObject,
    mut v_a_2881_: *mut crate::leanh::LeanObject,
    mut v_a_2882_: *mut crate::leanh::LeanObject,
    mut v_a_2883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2884_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
        v_a_2876_, v_b_2877_, v_x_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_,
    );
    crate::leanh::lean_dec(v_a_2882_);
    crate::leanh::lean_dec_ref(v_a_2881_);
    crate::leanh::lean_dec(v_a_2880_);
    crate::leanh::lean_dec_ref(v_a_2879_);
    crate::leanh::lean_dec(v_x_2878_);
    return v_res_2884_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(
    mut v_x_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2892_) {
        0 => {
            let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2893_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0;
            return v___x_2893_;
        }
        1 => {
            let mut v_red_2894_: u8 = 0;
            v_red_2894_ = crate::leanh::lean_ctor_get_uint8(v_x_2892_, 0 as u32);
            match v_red_2894_ {
                0 => {
                    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2895_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1;
                    return v___x_2895_;
                }
                1 => {
                    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2896_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2;
                    return v___x_2896_;
                }
                2 => {
                    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2897_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3;
                    return v___x_2897_;
                }
                3 => {
                    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2898_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4;
                    return v___x_2898_;
                }
                _ => {
                    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2899_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5;
                    return v___x_2899_;
                }
            }
        }
        _ => {
            let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2900_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6;
            return v___x_2900_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___boxed(
    mut v_x_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_x_2901_);
    crate::leanh::lean_dec(v_x_2901_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(
    mut v_e_2903_: *mut crate::leanh::LeanObject,
    mut v___y_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_unused_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2906_ = l_Lean_Expr_hasMVar(v_e_2903_);
                if v___x_2906_ == 0 {
                    v___x_2907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2907_, 0, v_e_2903_);
                    return v___x_2907_;
                } else {
                    v___x_2908_ = lean_st_ref_get(v___y_2904_);
                    v_mctx_2909_ = crate::leanh::lean_ctor_get(v___x_2908_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_2909_);
                    crate::leanh::lean_dec(v___x_2908_);
                    v___x_2910_ = l_Lean_instantiateMVarsCore(v_mctx_2909_, v_e_2903_);
                    v_fst_2911_ = crate::leanh::lean_ctor_get(v___x_2910_, 0);
                    crate::leanh::lean_inc(v_fst_2911_);
                    v_snd_2912_ = crate::leanh::lean_ctor_get(v___x_2910_, 1);
                    crate::leanh::lean_inc(v_snd_2912_);
                    crate::leanh::lean_dec_ref(v___x_2910_);
                    v___x_2913_ = lean_st_ref_take(v___y_2904_);
                    v_cache_2914_ = crate::leanh::lean_ctor_get(v___x_2913_, 1);
                    v_zetaDeltaFVarIds_2915_ = crate::leanh::lean_ctor_get(v___x_2913_, 2);
                    v_postponed_2916_ = crate::leanh::lean_ctor_get(v___x_2913_, 3);
                    v_diag_2917_ = crate::leanh::lean_ctor_get(v___x_2913_, 4);
                    v_isSharedCheck_2926_ = (!crate::leanh::lean_is_exclusive(v___x_2913_)) as u8;
                    if v_isSharedCheck_2926_ == 0 {
                        v_unused_2927_ = crate::leanh::lean_ctor_get(v___x_2913_, 0);
                        crate::leanh::lean_dec(v_unused_2927_);
                        v___x_2919_ = v___x_2913_;
                        v_isShared_2920_ = v_isSharedCheck_2926_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_2917_);
                        crate::leanh::lean_inc(v_postponed_2916_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_2915_);
                        crate::leanh::lean_inc(v_cache_2914_);
                        crate::leanh::lean_dec(v___x_2913_);
                        v___x_2919_ = crate::leanh::lean_box(0);
                        v_isShared_2920_ = v_isSharedCheck_2926_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2919_, 0, v_snd_2912_);
                    v___x_2922_ = v___x_2919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_snd_2912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_cache_2914_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2925_,
                        2,
                        v_zetaDeltaFVarIds_2915_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_postponed_2916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_diag_2917_);
                    v___x_2922_ = v_reuseFailAlloc_2925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2923_ = lean_st_ref_set(v___y_2904_, v___x_2922_);
                v___x_2924_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2924_, 0, v_fst_2911_);
                return v___x_2924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(
    mut v_e_2928_: *mut crate::leanh::LeanObject,
    mut v___y_2929_: *mut crate::leanh::LeanObject,
    mut v___y_2930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2931_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_2928_, v___y_2929_);
    crate::leanh::lean_dec(v___y_2929_);
    return v_res_2931_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(
    mut v_e_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_2932_, v___y_2936_);
    return v___x_2940_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(
    mut v_e_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
    mut v___y_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
    mut v___y_2946_: *mut crate::leanh::LeanObject,
    mut v___y_2947_: *mut crate::leanh::LeanObject,
    mut v___y_2948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2949_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(
            v_e_2941_,
            v___y_2942_,
            v___y_2943_,
            v___y_2944_,
            v___y_2945_,
            v___y_2946_,
            v___y_2947_,
        );
    crate::leanh::lean_dec(v___y_2947_);
    crate::leanh::lean_dec_ref(v___y_2946_);
    crate::leanh::lean_dec(v___y_2945_);
    crate::leanh::lean_dec_ref(v___y_2944_);
    crate::leanh::lean_dec(v___y_2943_);
    crate::leanh::lean_dec_ref(v___y_2942_);
    return v_res_2949_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(
    mut v_a_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
    mut v___y_2954_: *mut crate::leanh::LeanObject,
    mut v___y_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2958_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2950_,
        v___y_2951_,
        v___y_2952_,
        v___y_2953_,
        v___y_2954_,
        v___y_2955_,
        v___y_2956_,
    );
    return v___x_2958_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg___boxed(
    mut v_a_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
    mut v___y_2961_: *mut crate::leanh::LeanObject,
    mut v___y_2962_: *mut crate::leanh::LeanObject,
    mut v___y_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2967_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(v_a_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
    crate::leanh::lean_dec(v___y_2965_);
    crate::leanh::lean_dec_ref(v___y_2964_);
    crate::leanh::lean_dec(v___y_2963_);
    crate::leanh::lean_dec_ref(v___y_2962_);
    crate::leanh::lean_dec(v___y_2961_);
    crate::leanh::lean_dec_ref(v___y_2960_);
    return v_res_2967_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(
    mut v_00_u03b1_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2977_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2969_,
        v___y_2970_,
        v___y_2971_,
        v___y_2972_,
        v___y_2973_,
        v___y_2974_,
        v___y_2975_,
    );
    return v___x_2977_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___boxed(
    mut v_00_u03b1_2978_: *mut crate::leanh::LeanObject,
    mut v_a_2979_: *mut crate::leanh::LeanObject,
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
    mut v___y_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2987_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(v_00_u03b1_2978_, v_a_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
    crate::leanh::lean_dec(v___y_2985_);
    crate::leanh::lean_dec_ref(v___y_2984_);
    crate::leanh::lean_dec(v___y_2983_);
    crate::leanh::lean_dec_ref(v___y_2982_);
    crate::leanh::lean_dec(v___y_2981_);
    crate::leanh::lean_dec_ref(v___y_2980_);
    return v_res_2987_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(
    mut v_a_2988_: *mut crate::leanh::LeanObject,
    mut v___x_2989_: *mut crate::leanh::LeanObject,
    mut v___x_2990_: u8,
    mut v_b_2991_: *mut crate::leanh::LeanObject,
    mut v_mk_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_a_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_a_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_a_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v_a_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_2989_);
                v___x_3000_ = l_Lean_Elab_Term_elabTerm(
                    v_a_2988_,
                    v___x_2989_,
                    v___x_2990_,
                    v___x_2990_,
                    v___y_2993_,
                    v___y_2994_,
                    v___y_2995_,
                    v___y_2996_,
                    v___y_2997_,
                    v___y_2998_,
                );
                if crate::leanh::lean_obj_tag(v___x_3000_) == 0 {
                    v_a_3001_ = crate::leanh::lean_ctor_get(v___x_3000_, 0);
                    crate::leanh::lean_inc(v_a_3001_);
                    crate::leanh::lean_dec_ref_known(v___x_3000_, 1);
                    v___x_3002_ = l_Lean_Elab_Term_elabTerm(
                        v_b_2991_,
                        v___x_2989_,
                        v___x_2990_,
                        v___x_2990_,
                        v___y_2993_,
                        v___y_2994_,
                        v___y_2995_,
                        v___y_2996_,
                        v___y_2997_,
                        v___y_2998_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3002_) == 0 {
                        v_a_3003_ = crate::leanh::lean_ctor_get(v___x_3002_, 0);
                        crate::leanh::lean_inc(v_a_3003_);
                        crate::leanh::lean_dec_ref_known(v___x_3002_, 1);
                        crate::leanh::lean_inc(v___y_2998_);
                        crate::leanh::lean_inc_ref(v___y_2997_);
                        crate::leanh::lean_inc(v___y_2996_);
                        crate::leanh::lean_inc_ref(v___y_2995_);
                        crate::leanh::lean_inc(v_a_3001_);
                        v___x_3004_ = lean_infer_type(
                            v_a_3001_,
                            v___y_2995_,
                            v___y_2996_,
                            v___y_2997_,
                            v___y_2998_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3004_) == 0 {
                            v_a_3005_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                            crate::leanh::lean_inc(v_a_3005_);
                            crate::leanh::lean_dec_ref_known(v___x_3004_, 1);
                            crate::leanh::lean_inc(v___y_2998_);
                            crate::leanh::lean_inc_ref(v___y_2997_);
                            crate::leanh::lean_inc(v___y_2996_);
                            crate::leanh::lean_inc_ref(v___y_2995_);
                            crate::leanh::lean_inc(v_a_3003_);
                            v___x_3006_ = lean_infer_type(
                                v_a_3003_,
                                v___y_2995_,
                                v___y_2996_,
                                v___y_2997_,
                                v___y_2998_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3006_) == 0 {
                                v_a_3007_ = crate::leanh::lean_ctor_get(v___x_3006_, 0);
                                crate::leanh::lean_inc(v_a_3007_);
                                crate::leanh::lean_dec_ref_known(v___x_3006_, 1);
                                v___x_3008_ = l_Lean_Meta_isExprDefEqGuarded(
                                    v_a_3005_,
                                    v_a_3007_,
                                    v___y_2995_,
                                    v___y_2996_,
                                    v___y_2997_,
                                    v___y_2998_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3008_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3008_, 1);
                                    v___x_3009_ = 0;
                                    v___x_3010_ =
                                        l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                                            v___x_3009_,
                                            v___y_2993_,
                                            v___y_2994_,
                                            v___y_2995_,
                                            v___y_2996_,
                                            v___y_2997_,
                                            v___y_2998_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_3010_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3010_, 1);
                                        v___x_3011_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_3001_, v___y_2996_);
                                        v_a_3012_ = crate::leanh::lean_ctor_get(v___x_3011_, 0);
                                        crate::leanh::lean_inc(v_a_3012_);
                                        crate::leanh::lean_dec_ref(v___x_3011_);
                                        v___x_3013_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_3003_, v___y_2996_);
                                        v_a_3014_ = crate::leanh::lean_ctor_get(v___x_3013_, 0);
                                        crate::leanh::lean_inc(v_a_3014_);
                                        crate::leanh::lean_dec_ref(v___x_3013_);
                                        v___x_3015_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                                            v_a_3012_,
                                            v_a_3014_,
                                            v_mk_2992_,
                                            v___y_2995_,
                                            v___y_2996_,
                                            v___y_2997_,
                                            v___y_2998_,
                                        );
                                        crate::leanh::lean_dec(v___y_2998_);
                                        crate::leanh::lean_dec_ref(v___y_2997_);
                                        crate::leanh::lean_dec(v___y_2996_);
                                        crate::leanh::lean_dec_ref(v___y_2995_);
                                        return v___x_3015_;
                                    } else {
                                        crate::leanh::lean_dec(v_a_3003_);
                                        crate::leanh::lean_dec(v_a_3001_);
                                        crate::leanh::lean_dec(v___y_2998_);
                                        crate::leanh::lean_dec_ref(v___y_2997_);
                                        crate::leanh::lean_dec(v___y_2996_);
                                        crate::leanh::lean_dec_ref(v___y_2995_);
                                        v_a_3016_ = crate::leanh::lean_ctor_get(v___x_3010_, 0);
                                        v_isSharedCheck_3023_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3010_)) as u8;
                                        if v_isSharedCheck_3023_ == 0 {
                                            v___x_3018_ = v___x_3010_;
                                            v_isShared_3019_ = v_isSharedCheck_3023_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3016_);
                                            crate::leanh::lean_dec(v___x_3010_);
                                            v___x_3018_ = crate::leanh::lean_box(0);
                                            v_isShared_3019_ = v_isSharedCheck_3023_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3003_);
                                    crate::leanh::lean_dec(v_a_3001_);
                                    crate::leanh::lean_dec(v___y_2998_);
                                    crate::leanh::lean_dec_ref(v___y_2997_);
                                    crate::leanh::lean_dec(v___y_2996_);
                                    crate::leanh::lean_dec_ref(v___y_2995_);
                                    return v___x_3008_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3005_);
                                crate::leanh::lean_dec(v_a_3003_);
                                crate::leanh::lean_dec(v_a_3001_);
                                crate::leanh::lean_dec(v___y_2998_);
                                crate::leanh::lean_dec_ref(v___y_2997_);
                                crate::leanh::lean_dec(v___y_2996_);
                                crate::leanh::lean_dec_ref(v___y_2995_);
                                v_a_3024_ = crate::leanh::lean_ctor_get(v___x_3006_, 0);
                                v_isSharedCheck_3031_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3006_)) as u8;
                                if v_isSharedCheck_3031_ == 0 {
                                    v___x_3026_ = v___x_3006_;
                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3024_);
                                    crate::leanh::lean_dec(v___x_3006_);
                                    v___x_3026_ = crate::leanh::lean_box(0);
                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3003_);
                            crate::leanh::lean_dec(v_a_3001_);
                            crate::leanh::lean_dec(v___y_2998_);
                            crate::leanh::lean_dec_ref(v___y_2997_);
                            crate::leanh::lean_dec(v___y_2996_);
                            crate::leanh::lean_dec_ref(v___y_2995_);
                            v_a_3032_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                            v_isSharedCheck_3039_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3004_)) as u8;
                            if v_isSharedCheck_3039_ == 0 {
                                v___x_3034_ = v___x_3004_;
                                v_isShared_3035_ = v_isSharedCheck_3039_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3032_);
                                crate::leanh::lean_dec(v___x_3004_);
                                v___x_3034_ = crate::leanh::lean_box(0);
                                v_isShared_3035_ = v_isSharedCheck_3039_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3001_);
                        crate::leanh::lean_dec(v___y_2998_);
                        crate::leanh::lean_dec_ref(v___y_2997_);
                        crate::leanh::lean_dec(v___y_2996_);
                        crate::leanh::lean_dec_ref(v___y_2995_);
                        v_a_3040_ = crate::leanh::lean_ctor_get(v___x_3002_, 0);
                        v_isSharedCheck_3047_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3002_)) as u8;
                        if v_isSharedCheck_3047_ == 0 {
                            v___x_3042_ = v___x_3002_;
                            v_isShared_3043_ = v_isSharedCheck_3047_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3040_);
                            crate::leanh::lean_dec(v___x_3002_);
                            v___x_3042_ = crate::leanh::lean_box(0);
                            v_isShared_3043_ = v_isSharedCheck_3047_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2998_);
                    crate::leanh::lean_dec_ref(v___y_2997_);
                    crate::leanh::lean_dec(v___y_2996_);
                    crate::leanh::lean_dec_ref(v___y_2995_);
                    crate::leanh::lean_dec(v_b_2991_);
                    crate::leanh::lean_dec(v___x_2989_);
                    v_a_3048_ = crate::leanh::lean_ctor_get(v___x_3000_, 0);
                    v_isSharedCheck_3055_ = (!crate::leanh::lean_is_exclusive(v___x_3000_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v___x_3050_ = v___x_3000_;
                        v_isShared_3051_ = v_isSharedCheck_3055_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3048_);
                        crate::leanh::lean_dec(v___x_3000_);
                        v___x_3050_ = crate::leanh::lean_box(0);
                        v_isShared_3051_ = v_isSharedCheck_3055_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3019_ == 0 {
                    v___x_3021_ = v___x_3018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
                    v___x_3021_ = v_reuseFailAlloc_3022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3021_;
            }
            3 => {
                if v_isShared_3027_ == 0 {
                    v___x_3029_ = v___x_3026_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
                    v___x_3029_ = v_reuseFailAlloc_3030_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3029_;
            }
            5 => {
                if v_isShared_3035_ == 0 {
                    v___x_3037_ = v___x_3034_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3037_;
            }
            7 => {
                if v_isShared_3043_ == 0 {
                    v___x_3045_ = v___x_3042_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
                    v___x_3045_ = v_reuseFailAlloc_3046_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3045_;
            }
            9 => {
                if v_isShared_3051_ == 0 {
                    v___x_3053_ = v___x_3050_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
                    v___x_3053_ = v_reuseFailAlloc_3054_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed(
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v___x_3057_: *mut crate::leanh::LeanObject,
    mut v___x_3058_: *mut crate::leanh::LeanObject,
    mut v_b_3059_: *mut crate::leanh::LeanObject,
    mut v_mk_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
    mut v___y_3063_: *mut crate::leanh::LeanObject,
    mut v___y_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1677__boxed_3068_: u8 = 0;
    let mut v_res_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1677__boxed_3068_ = (crate::leanh::lean_unbox(v___x_3058_) as u8);
    v_res_3069_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(
        v_a_3056_,
        v___x_3057_,
        v___x_1677__boxed_3068_,
        v_b_3059_,
        v_mk_3060_,
        v___y_3061_,
        v___y_3062_,
        v___y_3063_,
        v___y_3064_,
        v___y_3065_,
        v___y_3066_,
    );
    crate::leanh::lean_dec(v___y_3062_);
    crate::leanh::lean_dec_ref(v___y_3061_);
    crate::leanh::lean_dec(v_mk_3060_);
    return v_res_3069_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(
    mut v_mk_3070_: *mut crate::leanh::LeanObject,
    mut v_a_3071_: *mut crate::leanh::LeanObject,
    mut v_b_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v_a_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
    mut v_a_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3080_ = crate::leanh::lean_box(0);
    v___x_3081_ = 1;
    v___x_3082_ = crate::leanh::lean_box((v___x_3081_) as usize);
    v___f_3083_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        5,
    );
    crate::leanh::lean_closure_set(v___f_3083_, 0, v_a_3071_);
    crate::leanh::lean_closure_set(v___f_3083_, 1, v___x_3080_);
    crate::leanh::lean_closure_set(v___f_3083_, 2, v___x_3082_);
    crate::leanh::lean_closure_set(v___f_3083_, 3, v_b_3072_);
    crate::leanh::lean_closure_set(v___f_3083_, 4, v_mk_3070_);
    v___x_3084_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v___f_3083_,
        v_a_3073_,
        v_a_3074_,
        v_a_3075_,
        v_a_3076_,
        v_a_3077_,
        v_a_3078_,
    );
    return v___x_3084_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___boxed(
    mut v_mk_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
    mut v_b_3087_: *mut crate::leanh::LeanObject,
    mut v_a_3088_: *mut crate::leanh::LeanObject,
    mut v_a_3089_: *mut crate::leanh::LeanObject,
    mut v_a_3090_: *mut crate::leanh::LeanObject,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
    mut v_a_3092_: *mut crate::leanh::LeanObject,
    mut v_a_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3095_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(
        v_mk_3085_, v_a_3086_, v_b_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_,
        v_a_3093_,
    );
    crate::leanh::lean_dec(v_a_3093_);
    crate::leanh::lean_dec_ref(v_a_3092_);
    crate::leanh::lean_dec(v_a_3091_);
    crate::leanh::lean_dec_ref(v_a_3090_);
    crate::leanh::lean_dec(v_a_3089_);
    crate::leanh::lean_dec_ref(v_a_3088_);
    return v_res_3095_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3096_ = crate::leanh::lean_box(0);
    v___x_3097_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3098_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3098_, 0, v___x_3097_);
    crate::leanh::lean_ctor_set(v___x_3098_, 1, v___x_3096_);
    return v___x_3098_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3100_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
    v___x_3101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3101_, 0, v___x_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___boxed(
    mut v___y_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
    return v_res_3103_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(
    mut v_00_u03b1_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
    return v___x_3114_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___boxed(
    mut v_00_u03b1_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(v_00_u03b1_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
    crate::leanh::lean_dec(v___y_3123_);
    crate::leanh::lean_dec_ref(v___y_3122_);
    crate::leanh::lean_dec(v___y_3121_);
    crate::leanh::lean_dec_ref(v___y_3120_);
    crate::leanh::lean_dec(v___y_3119_);
    crate::leanh::lean_dec_ref(v___y_3118_);
    crate::leanh::lean_dec(v___y_3117_);
    crate::leanh::lean_dec_ref(v___y_3116_);
    return v_res_3125_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(
    mut v_msgData_3126_: *mut crate::leanh::LeanObject,
    mut v___y_3127_: *mut crate::leanh::LeanObject,
    mut v___y_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
    mut v___y_3130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = lean_st_ref_get(v___y_3130_);
    v_env_3133_ = crate::leanh::lean_ctor_get(v___x_3132_, 0);
    crate::leanh::lean_inc_ref(v_env_3133_);
    crate::leanh::lean_dec(v___x_3132_);
    v___x_3134_ = lean_st_ref_get(v___y_3128_);
    v_mctx_3135_ = crate::leanh::lean_ctor_get(v___x_3134_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3135_);
    crate::leanh::lean_dec(v___x_3134_);
    v_lctx_3136_ = crate::leanh::lean_ctor_get(v___y_3127_, 2);
    v_options_3137_ = crate::leanh::lean_ctor_get(v___y_3129_, 2);
    crate::leanh::lean_inc_ref(v_options_3137_);
    crate::leanh::lean_inc_ref(v_lctx_3136_);
    v___x_3138_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3138_, 0, v_env_3133_);
    crate::leanh::lean_ctor_set(v___x_3138_, 1, v_mctx_3135_);
    crate::leanh::lean_ctor_set(v___x_3138_, 2, v_lctx_3136_);
    crate::leanh::lean_ctor_set(v___x_3138_, 3, v_options_3137_);
    v___x_3139_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3139_, 0, v___x_3138_);
    crate::leanh::lean_ctor_set(v___x_3139_, 1, v_msgData_3126_);
    v___x_3140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3139_);
    return v___x_3140_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1___boxed(
    mut v_msgData_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msgData_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
    crate::leanh::lean_dec(v___y_3145_);
    crate::leanh::lean_dec_ref(v___y_3144_);
    crate::leanh::lean_dec(v___y_3143_);
    crate::leanh::lean_dec_ref(v___y_3142_);
    return v_res_3147_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(
    mut v_msg_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3154_ = crate::leanh::lean_ctor_get(v___y_3151_, 5);
                v___x_3155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
                v_a_3156_ = crate::leanh::lean_ctor_get(v___x_3155_, 0);
                v_isSharedCheck_3164_ = (!crate::leanh::lean_is_exclusive(v___x_3155_)) as u8;
                if v_isSharedCheck_3164_ == 0 {
                    v___x_3158_ = v___x_3155_;
                    v_isShared_3159_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3156_);
                    crate::leanh::lean_dec(v___x_3155_);
                    v___x_3158_ = crate::leanh::lean_box(0);
                    v_isShared_3159_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3154_);
                v___x_3160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3160_, 0, v_ref_3154_);
                crate::leanh::lean_ctor_set(v___x_3160_, 1, v_a_3156_);
                if v_isShared_3159_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3158_, 1);
                    crate::leanh::lean_ctor_set(v___x_3158_, 0, v___x_3160_);
                    v___x_3162_ = v___x_3158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
                    v___x_3162_ = v_reuseFailAlloc_3163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg___boxed(
    mut v_msg_3165_: *mut crate::leanh::LeanObject,
    mut v___y_3166_: *mut crate::leanh::LeanObject,
    mut v___y_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3171_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(
            v_msg_3165_,
            v___y_3166_,
            v___y_3167_,
            v___y_3168_,
            v___y_3169_,
        );
    crate::leanh::lean_dec(v___y_3169_);
    crate::leanh::lean_dec_ref(v___y_3168_);
    crate::leanh::lean_dec(v___y_3167_);
    crate::leanh::lean_dec_ref(v___y_3166_);
    return v_res_3171_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3173_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0;
    v___x_3174_ = l_Lean_stringToMessageData(v___x_3173_);
    return v___x_3174_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3176_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2;
    v___x_3177_ = l_Lean_stringToMessageData(v___x_3176_);
    return v___x_3177_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4;
    v___x_3180_ = l_Lean_stringToMessageData(v___x_3179_);
    return v___x_3180_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3182_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6;
    v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
    return v___x_3183_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(
    mut v___x_3184_: *mut crate::leanh::LeanObject,
    mut v_r_3185_: *mut crate::leanh::LeanObject,
    mut v_p_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
    mut v___y_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
    mut v___y_3191_: *mut crate::leanh::LeanObject,
    mut v___y_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut v_a_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___x_3184_) == 1 {
                    v_val_3196_ = crate::leanh::lean_ctor_get(v___x_3184_, 0);
                    crate::leanh::lean_inc_n(v_val_3196_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3184_, 1);
                    crate::leanh::lean_inc(v_p_3186_);
                    crate::leanh::lean_inc(v_r_3185_);
                    v___x_3197_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(
                        v_val_3196_,
                        v_r_3185_,
                        v_p_3186_,
                        v___y_3189_,
                        v___y_3190_,
                        v___y_3191_,
                        v___y_3192_,
                        v___y_3193_,
                        v___y_3194_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3197_) == 0 {
                        v_a_3198_ = crate::leanh::lean_ctor_get(v___x_3197_, 0);
                        v_isSharedCheck_3222_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3197_)) as u8;
                        if v_isSharedCheck_3222_ == 0 {
                            v___x_3200_ = v___x_3197_;
                            v_isShared_3201_ = v_isSharedCheck_3222_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3198_);
                            crate::leanh::lean_dec(v___x_3197_);
                            v___x_3200_ = crate::leanh::lean_box(0);
                            v_isShared_3201_ = v_isSharedCheck_3222_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3196_);
                        crate::leanh::lean_dec(v_p_3186_);
                        crate::leanh::lean_dec(v_r_3185_);
                        v_a_3223_ = crate::leanh::lean_ctor_get(v___x_3197_, 0);
                        v_isSharedCheck_3230_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3197_)) as u8;
                        if v_isSharedCheck_3230_ == 0 {
                            v___x_3225_ = v___x_3197_;
                            v_isShared_3226_ = v_isSharedCheck_3230_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3223_);
                            crate::leanh::lean_dec(v___x_3197_);
                            v___x_3225_ = crate::leanh::lean_box(0);
                            v_isShared_3226_ = v_isSharedCheck_3230_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_p_3186_);
                    crate::leanh::lean_dec(v_r_3185_);
                    crate::leanh::lean_dec(v___x_3184_);
                    v___x_3231_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                    return v___x_3231_;
                }
            }
            1 => {
                v___x_3202_ = (crate::leanh::lean_unbox(v_a_3198_) as u8);
                crate::leanh::lean_dec(v_a_3198_);
                if v___x_3202_ == 0 {
                    crate::leanh::lean_del_object(v___x_3200_);
                    v___x_3203_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1,
                    );
                    v___x_3204_ = l_Lean_MessageData_ofSyntax(v_r_3185_);
                    v___x_3205_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3205_, 0, v___x_3203_);
                    crate::leanh::lean_ctor_set(v___x_3205_, 1, v___x_3204_);
                    v___x_3206_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3,
                    );
                    v___x_3207_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3207_, 0, v___x_3205_);
                    crate::leanh::lean_ctor_set(v___x_3207_, 1, v___x_3206_);
                    v___x_3208_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_3196_);
                    crate::leanh::lean_dec(v_val_3196_);
                    v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
                    v___x_3210_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3210_, 0, v___x_3207_);
                    crate::leanh::lean_ctor_set(v___x_3210_, 1, v___x_3209_);
                    v___x_3211_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5,
                    );
                    v___x_3212_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3212_, 0, v___x_3210_);
                    crate::leanh::lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                    v___x_3213_ = l_Lean_MessageData_ofSyntax(v_p_3186_);
                    v___x_3214_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3214_, 0, v___x_3212_);
                    crate::leanh::lean_ctor_set(v___x_3214_, 1, v___x_3213_);
                    v___x_3215_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7,
                    );
                    v___x_3216_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3216_, 0, v___x_3214_);
                    crate::leanh::lean_ctor_set(v___x_3216_, 1, v___x_3215_);
                    v___x_3217_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3216_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
                    return v___x_3217_;
                } else {
                    crate::leanh::lean_dec(v_val_3196_);
                    crate::leanh::lean_dec(v_p_3186_);
                    crate::leanh::lean_dec(v_r_3185_);
                    v___x_3218_ = crate::leanh::lean_box(0);
                    if v_isShared_3201_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3200_, 0, v___x_3218_);
                        v___x_3220_ = v___x_3200_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                        v___x_3220_ = v_reuseFailAlloc_3221_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3220_;
            }
            3 => {
                if v_isShared_3226_ == 0 {
                    v___x_3228_ = v___x_3225_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
                    v___x_3228_ = v_reuseFailAlloc_3229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed(
    mut v___x_3232_: *mut crate::leanh::LeanObject,
    mut v_r_3233_: *mut crate::leanh::LeanObject,
    mut v_p_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3244_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(
        v___x_3232_,
        v_r_3233_,
        v_p_3234_,
        v___y_3235_,
        v___y_3236_,
        v___y_3237_,
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
    crate::leanh::lean_dec(v___y_3238_);
    crate::leanh::lean_dec_ref(v___y_3237_);
    crate::leanh::lean_dec(v___y_3236_);
    crate::leanh::lean_dec_ref(v___y_3235_);
    return v_res_3244_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(
    mut v_x_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
    mut v_a_3262_: *mut crate::leanh::LeanObject,
    mut v_a_3263_: *mut crate::leanh::LeanObject,
    mut v_a_3264_: *mut crate::leanh::LeanObject,
    mut v_a_3265_: *mut crate::leanh::LeanObject,
    mut v_a_3266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    v___x_3268_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
    crate::leanh::lean_inc(v_x_3258_);
    v___x_3269_ = l_Lean_Syntax_isOfKind(v_x_3258_, v___x_3268_);
    if v___x_3269_ == 0 {
        let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3271_: u8 = 0;
        v___x_3270_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
        crate::leanh::lean_inc(v_x_3258_);
        v___x_3271_ = l_Lean_Syntax_isOfKind(v_x_3258_, v___x_3270_);
        if v___x_3271_ == 0 {
            let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_x_3258_);
            v___x_3272_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
            return v___x_3272_;
        } else {
            let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_eq_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3276_: u8 = 0;
            v___x_3273_ = crate::leanh::lean_unsigned_to_nat(2);
            v_eq_3274_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3273_);
            v___x_3275_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
            crate::leanh::lean_inc(v_eq_3274_);
            v___x_3276_ = l_Lean_Syntax_isOfKind(v_eq_3274_, v___x_3275_);
            if v___x_3276_ == 0 {
                let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_eq_3274_);
                crate::leanh::lean_dec(v_x_3258_);
                v___x_3277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                return v___x_3277_;
            } else {
                let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_r_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_p_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___y_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3278_ = crate::leanh::lean_unsigned_to_nat(1);
                v_r_3279_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3278_);
                v___x_3280_ = crate::leanh::lean_unsigned_to_nat(3);
                v_p_3281_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3280_);
                crate::leanh::lean_dec(v_x_3258_);
                v___x_3282_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_3274_);
                v___y_3283_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    3,
                );
                crate::leanh::lean_closure_set(v___y_3283_, 0, v___x_3282_);
                crate::leanh::lean_closure_set(v___y_3283_, 1, v_r_3279_);
                crate::leanh::lean_closure_set(v___y_3283_, 2, v_p_3281_);
                v___x_3284_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___y_3283_,
                    v_a_3259_,
                    v_a_3260_,
                    v_a_3261_,
                    v_a_3262_,
                    v_a_3263_,
                    v_a_3264_,
                    v_a_3265_,
                    v_a_3266_,
                );
                return v___x_3284_;
            }
        }
    } else {
        let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_eq_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3288_: u8 = 0;
        v___x_3285_ = crate::leanh::lean_unsigned_to_nat(2);
        v_eq_3286_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3285_);
        v___x_3287_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
        crate::leanh::lean_inc(v_eq_3286_);
        v___x_3288_ = l_Lean_Syntax_isOfKind(v_eq_3286_, v___x_3287_);
        if v___x_3288_ == 0 {
            let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_eq_3286_);
            crate::leanh::lean_dec(v_x_3258_);
            v___x_3289_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
            return v___x_3289_;
        } else {
            let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___y_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3290_ = crate::leanh::lean_unsigned_to_nat(1);
            v_r_3291_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3290_);
            v___x_3292_ = crate::leanh::lean_unsigned_to_nat(3);
            v_p_3293_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3292_);
            crate::leanh::lean_dec(v_x_3258_);
            v___x_3294_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_3286_);
            v___y_3295_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed
                    as *mut core::ffi::c_void,
                12,
                3,
            );
            crate::leanh::lean_closure_set(v___y_3295_, 0, v___x_3294_);
            crate::leanh::lean_closure_set(v___y_3295_, 1, v_r_3291_);
            crate::leanh::lean_closure_set(v___y_3295_, 2, v_p_3293_);
            v___x_3296_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                v___y_3295_,
                v_a_3259_,
                v_a_3260_,
                v_a_3261_,
                v_a_3262_,
                v_a_3263_,
                v_a_3264_,
                v_a_3265_,
                v_a_3266_,
            );
            return v___x_3296_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed(
    mut v_x_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(
        v_x_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_,
        v_a_3305_,
    );
    crate::leanh::lean_dec(v_a_3305_);
    crate::leanh::lean_dec_ref(v_a_3304_);
    crate::leanh::lean_dec(v_a_3303_);
    crate::leanh::lean_dec_ref(v_a_3302_);
    crate::leanh::lean_dec(v_a_3301_);
    crate::leanh::lean_dec_ref(v_a_3300_);
    crate::leanh::lean_dec(v_a_3299_);
    crate::leanh::lean_dec_ref(v_a_3298_);
    return v_res_3307_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(
    mut v_00_u03b1_3308_: *mut crate::leanh::LeanObject,
    mut v_msg_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3319_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(
            v_msg_3309_,
            v___y_3314_,
            v___y_3315_,
            v___y_3316_,
            v___y_3317_,
        );
    return v___x_3319_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___boxed(
    mut v_00_u03b1_3320_: *mut crate::leanh::LeanObject,
    mut v_msg_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3331_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(
        v_00_u03b1_3320_,
        v_msg_3321_,
        v___y_3322_,
        v___y_3323_,
        v___y_3324_,
        v___y_3325_,
        v___y_3326_,
        v___y_3327_,
        v___y_3328_,
        v___y_3329_,
    );
    crate::leanh::lean_dec(v___y_3329_);
    crate::leanh::lean_dec_ref(v___y_3328_);
    crate::leanh::lean_dec(v___y_3327_);
    crate::leanh::lean_dec_ref(v___y_3326_);
    crate::leanh::lean_dec(v___y_3325_);
    crate::leanh::lean_dec_ref(v___y_3324_);
    crate::leanh::lean_dec(v___y_3323_);
    crate::leanh::lean_dec_ref(v___y_3322_);
    return v_res_3331_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3342_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3343_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
    v___x_3344_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3;
    v___x_3345_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_3346_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3342_,
        v___x_3343_,
        v___x_3344_,
        v___x_3345_,
    );
    return v___x_3346_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___boxed(
    mut v_a_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3348_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
    return v_res_3348_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3375_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3;
    v___x_3376_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6;
    v___x_3377_ = l_Lean_addBuiltinDeclarationRanges(v___x_3375_, v___x_3376_);
    return v___x_3377_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___boxed(
    mut v_a_3378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3379_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
    return v_res_3379_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(
    mut v_a_3380_: *mut crate::leanh::LeanObject,
    mut v_a_3381_: *mut crate::leanh::LeanObject,
    mut v_a_3382_: *mut crate::leanh::LeanObject,
    mut v_a_3383_: *mut crate::leanh::LeanObject,
    mut v_a_3384_: *mut crate::leanh::LeanObject,
    mut v_a_3385_: *mut crate::leanh::LeanObject,
    mut v_a_3386_: *mut crate::leanh::LeanObject,
    mut v_a_3387_: *mut crate::leanh::LeanObject,
    mut v_a_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(
        v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_,
        v_a_3388_,
    );
    return v___x_3390_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(
    mut v_a_3391_: *mut crate::leanh::LeanObject,
    mut v_a_3392_: *mut crate::leanh::LeanObject,
    mut v_a_3393_: *mut crate::leanh::LeanObject,
    mut v_a_3394_: *mut crate::leanh::LeanObject,
    mut v_a_3395_: *mut crate::leanh::LeanObject,
    mut v_a_3396_: *mut crate::leanh::LeanObject,
    mut v_a_3397_: *mut crate::leanh::LeanObject,
    mut v_a_3398_: *mut crate::leanh::LeanObject,
    mut v_a_3399_: *mut crate::leanh::LeanObject,
    mut v_a_3400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(
        v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_,
        v_a_3399_,
    );
    crate::leanh::lean_dec(v_a_3399_);
    crate::leanh::lean_dec_ref(v_a_3398_);
    crate::leanh::lean_dec(v_a_3397_);
    crate::leanh::lean_dec_ref(v_a_3396_);
    crate::leanh::lean_dec(v_a_3395_);
    crate::leanh::lean_dec_ref(v_a_3394_);
    crate::leanh::lean_dec(v_a_3393_);
    crate::leanh::lean_dec_ref(v_a_3392_);
    return v_res_3401_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3410_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_3411_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3412_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
    v___x_3413_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1;
    v___x_3414_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3411_,
        v___x_3412_,
        v___x_3413_,
        v___f_3410_,
    );
    return v___x_3414_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___boxed(
    mut v_a_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
    return v_res_3416_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3443_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1;
    v___x_3444_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6;
    v___x_3445_ = l_Lean_addBuiltinDeclarationRanges(v___x_3443_, v___x_3444_);
    return v___x_3445_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___boxed(
    mut v_a_3446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3447_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
    return v_res_3447_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(
    mut v_e_3448_: *mut crate::leanh::LeanObject,
    mut v___y_3449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3451_: u8 = 0;
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_unused_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3451_ = l_Lean_Expr_hasMVar(v_e_3448_);
                if v___x_3451_ == 0 {
                    v___x_3452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3452_, 0, v_e_3448_);
                    return v___x_3452_;
                } else {
                    v___x_3453_ = lean_st_ref_get(v___y_3449_);
                    v_mctx_3454_ = crate::leanh::lean_ctor_get(v___x_3453_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3454_);
                    crate::leanh::lean_dec(v___x_3453_);
                    v___x_3455_ = l_Lean_instantiateMVarsCore(v_mctx_3454_, v_e_3448_);
                    v_fst_3456_ = crate::leanh::lean_ctor_get(v___x_3455_, 0);
                    crate::leanh::lean_inc(v_fst_3456_);
                    v_snd_3457_ = crate::leanh::lean_ctor_get(v___x_3455_, 1);
                    crate::leanh::lean_inc(v_snd_3457_);
                    crate::leanh::lean_dec_ref(v___x_3455_);
                    v___x_3458_ = lean_st_ref_take(v___y_3449_);
                    v_cache_3459_ = crate::leanh::lean_ctor_get(v___x_3458_, 1);
                    v_zetaDeltaFVarIds_3460_ = crate::leanh::lean_ctor_get(v___x_3458_, 2);
                    v_postponed_3461_ = crate::leanh::lean_ctor_get(v___x_3458_, 3);
                    v_diag_3462_ = crate::leanh::lean_ctor_get(v___x_3458_, 4);
                    v_isSharedCheck_3471_ = (!crate::leanh::lean_is_exclusive(v___x_3458_)) as u8;
                    if v_isSharedCheck_3471_ == 0 {
                        v_unused_3472_ = crate::leanh::lean_ctor_get(v___x_3458_, 0);
                        crate::leanh::lean_dec(v_unused_3472_);
                        v___x_3464_ = v___x_3458_;
                        v_isShared_3465_ = v_isSharedCheck_3471_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3462_);
                        crate::leanh::lean_inc(v_postponed_3461_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3460_);
                        crate::leanh::lean_inc(v_cache_3459_);
                        crate::leanh::lean_dec(v___x_3458_);
                        v___x_3464_ = crate::leanh::lean_box(0);
                        v_isShared_3465_ = v_isSharedCheck_3471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v_snd_3457_);
                    v___x_3467_ = v___x_3464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3470_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_snd_3457_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_cache_3459_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3470_,
                        2,
                        v_zetaDeltaFVarIds_3460_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_postponed_3461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_diag_3462_);
                    v___x_3467_ = v_reuseFailAlloc_3470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3468_ = lean_st_ref_set(v___y_3449_, v___x_3467_);
                v___x_3469_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3469_, 0, v_fst_3456_);
                return v___x_3469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg___boxed(
    mut v_e_3473_: *mut crate::leanh::LeanObject,
    mut v___y_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_3473_, v___y_3474_);
    crate::leanh::lean_dec(v___y_3474_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(
    mut v_e_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_3477_, v___y_3483_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___boxed(
    mut v_e_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(
            v_e_3488_,
            v___y_3489_,
            v___y_3490_,
            v___y_3491_,
            v___y_3492_,
            v___y_3493_,
            v___y_3494_,
            v___y_3495_,
            v___y_3496_,
        );
    crate::leanh::lean_dec(v___y_3496_);
    crate::leanh::lean_dec_ref(v___y_3495_);
    crate::leanh::lean_dec(v___y_3494_);
    crate::leanh::lean_dec_ref(v___y_3493_);
    crate::leanh::lean_dec(v___y_3492_);
    crate::leanh::lean_dec_ref(v___y_3491_);
    crate::leanh::lean_dec(v___y_3490_);
    crate::leanh::lean_dec_ref(v___y_3489_);
    return v_res_3498_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3500_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0;
    v___x_3501_ = l_Lean_stringToMessageData(v___x_3500_);
    return v___x_3501_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3503_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2;
    v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
    return v___x_3504_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(
    mut v_getTgt_3505_: *mut crate::leanh::LeanObject,
    mut v_r_3506_: *mut crate::leanh::LeanObject,
    mut v_eq_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
    mut v___y_3512_: *mut crate::leanh::LeanObject,
    mut v___y_3513_: *mut crate::leanh::LeanObject,
    mut v___y_3514_: *mut crate::leanh::LeanObject,
    mut v___y_3515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_a_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3577_: u8 = 0;
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut v_a_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3515_);
                crate::leanh::lean_inc_ref(v___y_3514_);
                crate::leanh::lean_inc(v___y_3513_);
                crate::leanh::lean_inc_ref(v___y_3512_);
                crate::leanh::lean_inc(v___y_3511_);
                crate::leanh::lean_inc_ref(v___y_3510_);
                crate::leanh::lean_inc(v___y_3509_);
                crate::leanh::lean_inc_ref(v___y_3508_);
                v___x_3517_ = crate::leanh::lean_apply_9(
                    v_getTgt_3505_,
                    v___y_3508_,
                    v___y_3509_,
                    v___y_3510_,
                    v___y_3511_,
                    v___y_3512_,
                    v___y_3513_,
                    v___y_3514_,
                    v___y_3515_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3517_) == 0 {
                    v_a_3518_ = crate::leanh::lean_ctor_get(v___x_3517_, 0);
                    crate::leanh::lean_inc(v_a_3518_);
                    crate::leanh::lean_dec_ref_known(v___x_3517_, 1);
                    v___x_3519_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_a_3518_, v___y_3513_);
                    v_a_3520_ = crate::leanh::lean_ctor_get(v___x_3519_, 0);
                    v_isSharedCheck_3578_ = (!crate::leanh::lean_is_exclusive(v___x_3519_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v___x_3522_ = v___x_3519_;
                        v_isShared_3523_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3520_);
                        crate::leanh::lean_dec(v___x_3519_);
                        v___x_3522_ = crate::leanh::lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3515_);
                    crate::leanh::lean_dec_ref(v___y_3514_);
                    crate::leanh::lean_dec(v___y_3513_);
                    crate::leanh::lean_dec_ref(v___y_3512_);
                    crate::leanh::lean_dec(v___y_3511_);
                    crate::leanh::lean_dec_ref(v___y_3510_);
                    crate::leanh::lean_dec(v___y_3509_);
                    crate::leanh::lean_dec_ref(v___y_3508_);
                    crate::leanh::lean_dec(v_eq_3507_);
                    crate::leanh::lean_dec(v_r_3506_);
                    v_a_3579_ = crate::leanh::lean_ctor_get(v___x_3517_, 0);
                    v_isSharedCheck_3586_ = (!crate::leanh::lean_is_exclusive(v___x_3517_)) as u8;
                    if v_isSharedCheck_3586_ == 0 {
                        v___x_3581_ = v___x_3517_;
                        v_isShared_3582_ = v_isSharedCheck_3586_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3579_);
                        crate::leanh::lean_dec(v___x_3517_);
                        v___x_3581_ = crate::leanh::lean_box(0);
                        v_isShared_3582_ = v_isSharedCheck_3586_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_3515_);
                crate::leanh::lean_inc_ref(v___y_3514_);
                crate::leanh::lean_inc(v___y_3513_);
                crate::leanh::lean_inc_ref(v___y_3512_);
                crate::leanh::lean_inc(v_a_3520_);
                v___x_3524_ = lean_infer_type(
                    v_a_3520_,
                    v___y_3512_,
                    v___y_3513_,
                    v___y_3514_,
                    v___y_3515_,
                );
                if crate::leanh::lean_obj_tag(v___x_3524_) == 0 {
                    v_a_3525_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                    crate::leanh::lean_inc(v_a_3525_);
                    crate::leanh::lean_dec_ref_known(v___x_3524_, 1);
                    if v_isShared_3523_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3522_, 1);
                        crate::leanh::lean_ctor_set(v___x_3522_, 0, v_a_3525_);
                        v___x_3527_ = v___x_3522_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3525_);
                        v___x_3527_ = v_reuseFailAlloc_3569_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3522_);
                    crate::leanh::lean_dec(v_a_3520_);
                    crate::leanh::lean_dec(v___y_3515_);
                    crate::leanh::lean_dec_ref(v___y_3514_);
                    crate::leanh::lean_dec(v___y_3513_);
                    crate::leanh::lean_dec_ref(v___y_3512_);
                    crate::leanh::lean_dec(v___y_3511_);
                    crate::leanh::lean_dec_ref(v___y_3510_);
                    crate::leanh::lean_dec(v___y_3509_);
                    crate::leanh::lean_dec_ref(v___y_3508_);
                    crate::leanh::lean_dec(v_eq_3507_);
                    crate::leanh::lean_dec(v_r_3506_);
                    v_a_3570_ = crate::leanh::lean_ctor_get(v___x_3524_, 0);
                    v_isSharedCheck_3577_ = (!crate::leanh::lean_is_exclusive(v___x_3524_)) as u8;
                    if v_isSharedCheck_3577_ == 0 {
                        v___x_3572_ = v___x_3524_;
                        v_isShared_3573_ = v_isSharedCheck_3577_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3570_);
                        crate::leanh::lean_dec(v___x_3524_);
                        v___x_3572_ = crate::leanh::lean_box(0);
                        v_isShared_3573_ = v_isSharedCheck_3577_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3528_ = 0;
                v___x_3529_ = l_Lean_Elab_Tactic_elabTerm(
                    v_r_3506_,
                    v___x_3527_,
                    v___x_3528_,
                    v___y_3508_,
                    v___y_3509_,
                    v___y_3510_,
                    v___y_3511_,
                    v___y_3512_,
                    v___y_3513_,
                    v___y_3514_,
                    v___y_3515_,
                );
                crate::leanh::lean_dec(v___y_3511_);
                crate::leanh::lean_dec_ref(v___y_3510_);
                crate::leanh::lean_dec(v___y_3509_);
                crate::leanh::lean_dec_ref(v___y_3508_);
                if crate::leanh::lean_obj_tag(v___x_3529_) == 0 {
                    v_a_3530_ = crate::leanh::lean_ctor_get(v___x_3529_, 0);
                    crate::leanh::lean_inc(v_a_3530_);
                    crate::leanh::lean_dec_ref_known(v___x_3529_, 1);
                    v___x_3531_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_3507_);
                    if crate::leanh::lean_obj_tag(v___x_3531_) == 1 {
                        v_val_3532_ = crate::leanh::lean_ctor_get(v___x_3531_, 0);
                        crate::leanh::lean_inc(v_val_3532_);
                        crate::leanh::lean_dec_ref_known(v___x_3531_, 1);
                        crate::leanh::lean_inc(v_a_3520_);
                        crate::leanh::lean_inc(v_a_3530_);
                        v___x_3533_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                            v_a_3530_,
                            v_a_3520_,
                            v_val_3532_,
                            v___y_3512_,
                            v___y_3513_,
                            v___y_3514_,
                            v___y_3515_,
                        );
                        crate::leanh::lean_dec(v_val_3532_);
                        if crate::leanh::lean_obj_tag(v___x_3533_) == 0 {
                            v_a_3534_ = crate::leanh::lean_ctor_get(v___x_3533_, 0);
                            v_isSharedCheck_3551_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3533_)) as u8;
                            if v_isSharedCheck_3551_ == 0 {
                                v___x_3536_ = v___x_3533_;
                                v_isShared_3537_ = v_isSharedCheck_3551_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3534_);
                                crate::leanh::lean_dec(v___x_3533_);
                                v___x_3536_ = crate::leanh::lean_box(0);
                                v_isShared_3537_ = v_isSharedCheck_3551_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3530_);
                            crate::leanh::lean_dec(v_a_3520_);
                            crate::leanh::lean_dec(v___y_3515_);
                            crate::leanh::lean_dec_ref(v___y_3514_);
                            crate::leanh::lean_dec(v___y_3513_);
                            crate::leanh::lean_dec_ref(v___y_3512_);
                            v_a_3552_ = crate::leanh::lean_ctor_get(v___x_3533_, 0);
                            v_isSharedCheck_3559_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3533_)) as u8;
                            if v_isSharedCheck_3559_ == 0 {
                                v___x_3554_ = v___x_3533_;
                                v_isShared_3555_ = v_isSharedCheck_3559_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3552_);
                                crate::leanh::lean_dec(v___x_3533_);
                                v___x_3554_ = crate::leanh::lean_box(0);
                                v_isShared_3555_ = v_isSharedCheck_3559_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3531_);
                        crate::leanh::lean_dec(v_a_3530_);
                        crate::leanh::lean_dec(v_a_3520_);
                        crate::leanh::lean_dec(v___y_3515_);
                        crate::leanh::lean_dec_ref(v___y_3514_);
                        crate::leanh::lean_dec(v___y_3513_);
                        crate::leanh::lean_dec_ref(v___y_3512_);
                        v___x_3560_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_3560_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3520_);
                    crate::leanh::lean_dec(v___y_3515_);
                    crate::leanh::lean_dec_ref(v___y_3514_);
                    crate::leanh::lean_dec(v___y_3513_);
                    crate::leanh::lean_dec_ref(v___y_3512_);
                    crate::leanh::lean_dec(v_eq_3507_);
                    v_a_3561_ = crate::leanh::lean_ctor_get(v___x_3529_, 0);
                    v_isSharedCheck_3568_ = (!crate::leanh::lean_is_exclusive(v___x_3529_)) as u8;
                    if v_isSharedCheck_3568_ == 0 {
                        v___x_3563_ = v___x_3529_;
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3561_);
                        crate::leanh::lean_dec(v___x_3529_);
                        v___x_3563_ = crate::leanh::lean_box(0);
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3538_ = (crate::leanh::lean_unbox(v_a_3534_) as u8);
                crate::leanh::lean_dec(v_a_3534_);
                if v___x_3538_ == 0 {
                    crate::leanh::lean_del_object(v___x_3536_);
                    v___x_3539_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1,
                    );
                    v___x_3540_ = l_Lean_indentExpr(v_a_3520_);
                    v___x_3541_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3541_, 0, v___x_3539_);
                    crate::leanh::lean_ctor_set(v___x_3541_, 1, v___x_3540_);
                    v___x_3542_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3,
                    );
                    v___x_3543_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3543_, 0, v___x_3541_);
                    crate::leanh::lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                    v___x_3544_ = l_Lean_indentExpr(v_a_3530_);
                    v___x_3545_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3545_, 0, v___x_3543_);
                    crate::leanh::lean_ctor_set(v___x_3545_, 1, v___x_3544_);
                    v___x_3546_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3545_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
                    crate::leanh::lean_dec(v___y_3515_);
                    crate::leanh::lean_dec_ref(v___y_3514_);
                    crate::leanh::lean_dec(v___y_3513_);
                    crate::leanh::lean_dec_ref(v___y_3512_);
                    return v___x_3546_;
                } else {
                    crate::leanh::lean_dec(v_a_3530_);
                    crate::leanh::lean_dec(v_a_3520_);
                    crate::leanh::lean_dec(v___y_3515_);
                    crate::leanh::lean_dec_ref(v___y_3514_);
                    crate::leanh::lean_dec(v___y_3513_);
                    crate::leanh::lean_dec_ref(v___y_3512_);
                    v___x_3547_ = crate::leanh::lean_box(0);
                    if v_isShared_3537_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3536_, 0, v___x_3547_);
                        v___x_3549_ = v___x_3536_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
                        v___x_3549_ = v_reuseFailAlloc_3550_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3549_;
            }
            5 => {
                if v_isShared_3555_ == 0 {
                    v___x_3557_ = v___x_3554_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
                    v___x_3557_ = v_reuseFailAlloc_3558_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3557_;
            }
            7 => {
                if v_isShared_3564_ == 0 {
                    v___x_3566_ = v___x_3563_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
                    v___x_3566_ = v_reuseFailAlloc_3567_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3566_;
            }
            9 => {
                if v_isShared_3573_ == 0 {
                    v___x_3575_ = v___x_3572_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
                    v___x_3575_ = v_reuseFailAlloc_3576_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3575_;
            }
            11 => {
                if v_isShared_3582_ == 0 {
                    v___x_3584_ = v___x_3581_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
                    v___x_3584_ = v_reuseFailAlloc_3585_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3584_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed(
    mut v_getTgt_3587_: *mut crate::leanh::LeanObject,
    mut v_r_3588_: *mut crate::leanh::LeanObject,
    mut v_eq_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
    mut v___y_3597_: *mut crate::leanh::LeanObject,
    mut v___y_3598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3599_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(
        v_getTgt_3587_,
        v_r_3588_,
        v_eq_3589_,
        v___y_3590_,
        v___y_3591_,
        v___y_3592_,
        v___y_3593_,
        v___y_3594_,
        v___y_3595_,
        v___y_3596_,
        v___y_3597_,
    );
    return v_res_3599_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(
    mut v_x_3614_: *mut crate::leanh::LeanObject,
    mut v_a_3615_: *mut crate::leanh::LeanObject,
    mut v_a_3616_: *mut crate::leanh::LeanObject,
    mut v_a_3617_: *mut crate::leanh::LeanObject,
    mut v_a_3618_: *mut crate::leanh::LeanObject,
    mut v_a_3619_: *mut crate::leanh::LeanObject,
    mut v_a_3620_: *mut crate::leanh::LeanObject,
    mut v_a_3621_: *mut crate::leanh::LeanObject,
    mut v_a_3622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eq_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getTgt_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3638_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
                crate::leanh::lean_inc(v_x_3614_);
                v___x_3639_ = l_Lean_Syntax_isOfKind(v_x_3614_, v___x_3638_);
                if v___x_3639_ == 0 {
                    v___x_3640_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3;
                    crate::leanh::lean_inc(v_x_3614_);
                    v___x_3641_ = l_Lean_Syntax_isOfKind(v_x_3614_, v___x_3640_);
                    if v___x_3641_ == 0 {
                        crate::leanh::lean_dec(v_x_3614_);
                        v___x_3642_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_3642_;
                    } else {
                        v___x_3643_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_eq_3644_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3643_);
                        v___x_3645_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3646_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3645_);
                        crate::leanh::lean_dec(v_x_3614_);
                        v___x_3647_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4;
                        v_eq_3625_ = v_eq_3644_;
                        v_r_3626_ = v___x_3646_;
                        v_getTgt_3627_ = v___x_3647_;
                        v___y_3628_ = v_a_3615_;
                        v___y_3629_ = v_a_3616_;
                        v___y_3630_ = v_a_3617_;
                        v___y_3631_ = v_a_3618_;
                        v___y_3632_ = v_a_3619_;
                        v___y_3633_ = v_a_3620_;
                        v___y_3634_ = v_a_3621_;
                        v___y_3635_ = v_a_3622_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3648_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_eq_3649_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3648_);
                    v___x_3650_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_3651_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3650_);
                    crate::leanh::lean_dec(v_x_3614_);
                    v___x_3652_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5;
                    v_eq_3625_ = v_eq_3649_;
                    v_r_3626_ = v___x_3651_;
                    v_getTgt_3627_ = v___x_3652_;
                    v___y_3628_ = v_a_3615_;
                    v___y_3629_ = v_a_3616_;
                    v___y_3630_ = v_a_3617_;
                    v___y_3631_ = v_a_3618_;
                    v___y_3632_ = v_a_3619_;
                    v___y_3633_ = v_a_3620_;
                    v___y_3634_ = v_a_3621_;
                    v___y_3635_ = v_a_3622_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_getTgt_3627_);
                v___f_3636_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3636_, 0, v_getTgt_3627_);
                crate::leanh::lean_closure_set(v___f_3636_, 1, v_r_3626_);
                crate::leanh::lean_closure_set(v___f_3636_, 2, v_eq_3625_);
                v___x_3637_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_3636_,
                    v___y_3628_,
                    v___y_3629_,
                    v___y_3630_,
                    v___y_3631_,
                    v___y_3632_,
                    v___y_3633_,
                    v___y_3634_,
                    v___y_3635_,
                );
                return v___x_3637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed(
    mut v_x_3653_: *mut crate::leanh::LeanObject,
    mut v_a_3654_: *mut crate::leanh::LeanObject,
    mut v_a_3655_: *mut crate::leanh::LeanObject,
    mut v_a_3656_: *mut crate::leanh::LeanObject,
    mut v_a_3657_: *mut crate::leanh::LeanObject,
    mut v_a_3658_: *mut crate::leanh::LeanObject,
    mut v_a_3659_: *mut crate::leanh::LeanObject,
    mut v_a_3660_: *mut crate::leanh::LeanObject,
    mut v_a_3661_: *mut crate::leanh::LeanObject,
    mut v_a_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3663_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(
        v_x_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_,
        v_a_3661_,
    );
    crate::leanh::lean_dec(v_a_3661_);
    crate::leanh::lean_dec_ref(v_a_3660_);
    crate::leanh::lean_dec(v_a_3659_);
    crate::leanh::lean_dec_ref(v_a_3658_);
    crate::leanh::lean_dec(v_a_3657_);
    crate::leanh::lean_dec_ref(v_a_3656_);
    crate::leanh::lean_dec(v_a_3655_);
    crate::leanh::lean_dec_ref(v_a_3654_);
    return v_res_3663_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3672_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3673_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
    v___x_3674_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1;
    v___x_3675_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_3676_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3672_,
        v___x_3673_,
        v___x_3674_,
        v___x_3675_,
    );
    return v___x_3676_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___boxed(
    mut v_a_3677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3678_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
    return v_res_3678_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3705_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1;
    v___x_3706_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6;
    v___x_3707_ = l_Lean_addBuiltinDeclarationRanges(v___x_3705_, v___x_3706_);
    return v___x_3707_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___boxed(
    mut v_a_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3709_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
    return v_res_3709_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
    mut v_a_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
    mut v_a_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v_a_3718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(
        v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_,
        v_a_3718_,
    );
    return v___x_3720_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(
    mut v_a_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
    mut v_a_3723_: *mut crate::leanh::LeanObject,
    mut v_a_3724_: *mut crate::leanh::LeanObject,
    mut v_a_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3731_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(
        v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_,
        v_a_3729_,
    );
    crate::leanh::lean_dec(v_a_3729_);
    crate::leanh::lean_dec_ref(v_a_3728_);
    crate::leanh::lean_dec(v_a_3727_);
    crate::leanh::lean_dec_ref(v_a_3726_);
    crate::leanh::lean_dec(v_a_3725_);
    crate::leanh::lean_dec_ref(v_a_3724_);
    crate::leanh::lean_dec(v_a_3723_);
    crate::leanh::lean_dec_ref(v_a_3722_);
    return v_res_3731_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3740_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_3741_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3742_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3;
    v___x_3743_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1;
    v___x_3744_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3741_,
        v___x_3742_,
        v___x_3743_,
        v___f_3740_,
    );
    return v___x_3744_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___boxed(
    mut v_a_3745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3746_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
    return v_res_3746_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3773_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1;
    v___x_3774_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6;
    v___x_3775_ = l_Lean_addBuiltinDeclarationRanges(v___x_3773_, v___x_3774_);
    return v___x_3775_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___boxed(
    mut v_a_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3777_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
    return v_res_3777_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0;
    v___x_3780_ = l_Lean_stringToMessageData(v___x_3779_);
    return v___x_3780_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3782_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2;
    v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3785_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4;
    v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3788_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6;
    v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
    return v___x_3789_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3791_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8;
    v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
    return v___x_3792_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3794_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10;
    v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
    return v___x_3795_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3797_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12;
    v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
    return v___x_3798_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14;
    v___x_3801_ = l_Lean_stringToMessageData(v___x_3800_);
    return v___x_3801_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(
    mut v___x_3802_: *mut crate::leanh::LeanObject,
    mut v___x_3803_: u8,
    mut v_val_3804_: *mut crate::leanh::LeanObject,
    mut v_eq_3805_: *mut crate::leanh::LeanObject,
    mut v_c_3806_: *mut crate::leanh::LeanObject,
    mut v_ty_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
    mut v___y_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3862_: u8 = 0;
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3880_: u8 = 0;
    let mut v_a_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3888_: u8 = 0;
    let mut v_a_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_reuseFailAlloc_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecl_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3942_: u8 = 0;
    let mut v_a_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3946_: u8 = 0;
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3950_: u8 = 0;
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3965_: u8 = 0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut v_val_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_3802_);
                v___x_3952_ = l_Lean_Elab_Tactic_getFVarId(
                    v___x_3802_,
                    v___y_3808_,
                    v___y_3809_,
                    v___y_3810_,
                    v___y_3811_,
                    v___y_3812_,
                    v___y_3813_,
                    v___y_3814_,
                    v___y_3815_,
                );
                if crate::leanh::lean_obj_tag(v___x_3952_) == 0 {
                    v_a_3953_ = crate::leanh::lean_ctor_get(v___x_3952_, 0);
                    crate::leanh::lean_inc(v_a_3953_);
                    crate::leanh::lean_dec_ref_known(v___x_3952_, 1);
                    v_lctx_3954_ = crate::leanh::lean_ctor_get(v___y_3812_, 2);
                    crate::leanh::lean_inc_ref(v_lctx_3954_);
                    v___x_3955_ = lean_local_ctx_find(v_lctx_3954_, v_a_3953_);
                    if crate::leanh::lean_obj_tag(v___x_3955_) == 0 {
                        crate::leanh::lean_dec(v_ty_3807_);
                        crate::leanh::lean_dec(v_c_3806_);
                        crate::leanh::lean_dec(v_eq_3805_);
                        crate::leanh::lean_dec(v_val_3804_);
                        v___x_3956_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                        );
                        v___x_3957_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                        v___x_3958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3958_, 0, v___x_3956_);
                        crate::leanh::lean_ctor_set(v___x_3958_, 1, v___x_3957_);
                        v___x_3959_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
                        v___x_3960_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3960_, 0, v___x_3958_);
                        crate::leanh::lean_ctor_set(v___x_3960_, 1, v___x_3959_);
                        v___x_3961_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3960_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
                        crate::leanh::lean_dec_ref(v___y_3812_);
                        v_a_3962_ = crate::leanh::lean_ctor_get(v___x_3961_, 0);
                        v_isSharedCheck_3969_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3961_)) as u8;
                        if v_isSharedCheck_3969_ == 0 {
                            v___x_3964_ = v___x_3961_;
                            v_isShared_3965_ = v_isSharedCheck_3969_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3962_);
                            crate::leanh::lean_dec(v___x_3961_);
                            v___x_3964_ = crate::leanh::lean_box(0);
                            v_isShared_3965_ = v_isSharedCheck_3969_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v_val_3970_ = crate::leanh::lean_ctor_get(v___x_3955_, 0);
                        crate::leanh::lean_inc(v_val_3970_);
                        crate::leanh::lean_dec_ref_known(v___x_3955_, 1);
                        v_lDecl_3901_ = v_val_3970_;
                        v___y_3902_ = v___y_3808_;
                        v___y_3903_ = v___y_3809_;
                        v___y_3904_ = v___y_3810_;
                        v___y_3905_ = v___y_3811_;
                        v___y_3906_ = v___y_3812_;
                        v___y_3907_ = v___y_3813_;
                        v___y_3908_ = v___y_3814_;
                        v___y_3909_ = v___y_3815_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3812_);
                    crate::leanh::lean_dec(v_ty_3807_);
                    crate::leanh::lean_dec(v_c_3806_);
                    crate::leanh::lean_dec(v_eq_3805_);
                    crate::leanh::lean_dec(v_val_3804_);
                    crate::leanh::lean_dec(v___x_3802_);
                    v_a_3971_ = crate::leanh::lean_ctor_get(v___x_3952_, 0);
                    v_isSharedCheck_3978_ = (!crate::leanh::lean_is_exclusive(v___x_3952_)) as u8;
                    if v_isSharedCheck_3978_ == 0 {
                        v___x_3973_ = v___x_3952_;
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3971_);
                        crate::leanh::lean_dec(v___x_3952_);
                        v___x_3973_ = crate::leanh::lean_box(0);
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3827_ = l_Lean_LocalDecl_value_x3f(v___y_3818_, v___x_3803_);
                if crate::leanh::lean_obj_tag(v___x_3827_) == 0 {
                    crate::leanh::lean_dec_ref(v___y_3818_);
                    crate::leanh::lean_dec(v_eq_3805_);
                    if crate::leanh::lean_obj_tag(v_val_3804_) == 0 {
                        crate::leanh::lean_dec_ref(v___y_3823_);
                        crate::leanh::lean_dec(v___x_3802_);
                        v___x_3828_ = crate::leanh::lean_box(0);
                        v___x_3829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3828_);
                        return v___x_3829_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_val_3804_, 1);
                        v___x_3830_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_3831_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                        v___x_3832_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3832_, 0, v___x_3830_);
                        crate::leanh::lean_ctor_set(v___x_3832_, 1, v___x_3831_);
                        v___x_3833_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1,
                        );
                        v___x_3834_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3834_, 0, v___x_3832_);
                        crate::leanh::lean_ctor_set(v___x_3834_, 1, v___x_3833_);
                        v___x_3835_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3834_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
                        crate::leanh::lean_dec_ref(v___y_3823_);
                        return v___x_3835_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_val_3804_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3827_, 1);
                        crate::leanh::lean_dec_ref(v___y_3818_);
                        crate::leanh::lean_dec(v_eq_3805_);
                        v___x_3836_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_3837_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                        v___x_3838_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3838_, 0, v___x_3836_);
                        crate::leanh::lean_ctor_set(v___x_3838_, 1, v___x_3837_);
                        v___x_3839_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3,
                        );
                        v___x_3840_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3840_, 0, v___x_3838_);
                        crate::leanh::lean_ctor_set(v___x_3840_, 1, v___x_3839_);
                        v___x_3841_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3840_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
                        crate::leanh::lean_dec_ref(v___y_3823_);
                        return v___x_3841_;
                    } else {
                        if crate::leanh::lean_obj_tag(v_eq_3805_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_val_3804_, 1);
                            crate::leanh::lean_dec_ref_known(v___x_3827_, 1);
                            crate::leanh::lean_dec_ref(v___y_3823_);
                            crate::leanh::lean_dec_ref(v___y_3818_);
                            crate::leanh::lean_dec(v___x_3802_);
                            v___x_3842_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_3842_;
                        } else {
                            v_val_3843_ = crate::leanh::lean_ctor_get(v___x_3827_, 0);
                            crate::leanh::lean_inc(v_val_3843_);
                            crate::leanh::lean_dec_ref_known(v___x_3827_, 1);
                            v_val_3844_ = crate::leanh::lean_ctor_get(v_val_3804_, 0);
                            crate::leanh::lean_inc(v_val_3844_);
                            crate::leanh::lean_dec_ref_known(v_val_3804_, 1);
                            v_val_3845_ = crate::leanh::lean_ctor_get(v_eq_3805_, 0);
                            crate::leanh::lean_inc(v_val_3845_);
                            crate::leanh::lean_dec_ref_known(v_eq_3805_, 1);
                            v___x_3846_ =
                                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_3845_);
                            if crate::leanh::lean_obj_tag(v___x_3846_) == 1 {
                                v_val_3847_ = crate::leanh::lean_ctor_get(v___x_3846_, 0);
                                v_isSharedCheck_3898_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3846_)) as u8;
                                if v_isSharedCheck_3898_ == 0 {
                                    v___x_3849_ = v___x_3846_;
                                    v_isShared_3850_ = v_isSharedCheck_3898_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3847_);
                                    crate::leanh::lean_dec(v___x_3846_);
                                    v___x_3849_ = crate::leanh::lean_box(0);
                                    v_isShared_3850_ = v_isSharedCheck_3898_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_3846_);
                                crate::leanh::lean_dec(v_val_3844_);
                                crate::leanh::lean_dec(v_val_3843_);
                                crate::leanh::lean_dec_ref(v___y_3823_);
                                crate::leanh::lean_dec_ref(v___y_3818_);
                                crate::leanh::lean_dec(v___x_3802_);
                                v___x_3899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                                return v___x_3899_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3851_ = l_Lean_LocalDecl_type(v___y_3818_);
                crate::leanh::lean_dec_ref(v___y_3818_);
                if v_isShared_3850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3851_);
                    v___x_3853_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3851_);
                    v___x_3853_ = v_reuseFailAlloc_3897_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3854_ = l_Lean_Elab_Tactic_elabTerm(
                    v_val_3844_,
                    v___x_3853_,
                    v___x_3803_,
                    v___y_3819_,
                    v___y_3820_,
                    v___y_3821_,
                    v___y_3822_,
                    v___y_3823_,
                    v___y_3824_,
                    v___y_3825_,
                    v___y_3826_,
                );
                if crate::leanh::lean_obj_tag(v___x_3854_) == 0 {
                    v_a_3855_ = crate::leanh::lean_ctor_get(v___x_3854_, 0);
                    crate::leanh::lean_inc_n(v_a_3855_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3854_, 1);
                    v___x_3856_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_3843_, v___y_3824_);
                    v_a_3857_ = crate::leanh::lean_ctor_get(v___x_3856_, 0);
                    crate::leanh::lean_inc_n(v_a_3857_, 2);
                    crate::leanh::lean_dec_ref(v___x_3856_);
                    v___x_3858_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                        v_a_3855_,
                        v_a_3857_,
                        v_val_3847_,
                        v___y_3823_,
                        v___y_3824_,
                        v___y_3825_,
                        v___y_3826_,
                    );
                    crate::leanh::lean_dec(v_val_3847_);
                    if crate::leanh::lean_obj_tag(v___x_3858_) == 0 {
                        v_a_3859_ = crate::leanh::lean_ctor_get(v___x_3858_, 0);
                        v_isSharedCheck_3880_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3858_)) as u8;
                        if v_isSharedCheck_3880_ == 0 {
                            v___x_3861_ = v___x_3858_;
                            v_isShared_3862_ = v_isSharedCheck_3880_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3859_);
                            crate::leanh::lean_dec(v___x_3858_);
                            v___x_3861_ = crate::leanh::lean_box(0);
                            v_isShared_3862_ = v_isSharedCheck_3880_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3857_);
                        crate::leanh::lean_dec(v_a_3855_);
                        crate::leanh::lean_dec_ref(v___y_3823_);
                        crate::leanh::lean_dec(v___x_3802_);
                        v_a_3881_ = crate::leanh::lean_ctor_get(v___x_3858_, 0);
                        v_isSharedCheck_3888_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3858_)) as u8;
                        if v_isSharedCheck_3888_ == 0 {
                            v___x_3883_ = v___x_3858_;
                            v_isShared_3884_ = v_isSharedCheck_3888_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3881_);
                            crate::leanh::lean_dec(v___x_3858_);
                            v___x_3883_ = crate::leanh::lean_box(0);
                            v_isShared_3884_ = v_isSharedCheck_3888_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_3847_);
                    crate::leanh::lean_dec(v_val_3843_);
                    crate::leanh::lean_dec_ref(v___y_3823_);
                    crate::leanh::lean_dec(v___x_3802_);
                    v_a_3889_ = crate::leanh::lean_ctor_get(v___x_3854_, 0);
                    v_isSharedCheck_3896_ = (!crate::leanh::lean_is_exclusive(v___x_3854_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3891_ = v___x_3854_;
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3889_);
                        crate::leanh::lean_dec(v___x_3854_);
                        v___x_3891_ = crate::leanh::lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3863_ = (crate::leanh::lean_unbox(v_a_3859_) as u8);
                crate::leanh::lean_dec(v_a_3859_);
                if v___x_3863_ == 0 {
                    crate::leanh::lean_del_object(v___x_3861_);
                    v___x_3864_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                    );
                    v___x_3865_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                    v___x_3866_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                    crate::leanh::lean_ctor_set(v___x_3866_, 1, v___x_3865_);
                    v___x_3867_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7,
                    );
                    v___x_3868_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3868_, 0, v___x_3866_);
                    crate::leanh::lean_ctor_set(v___x_3868_, 1, v___x_3867_);
                    v___x_3869_ = l_Lean_indentExpr(v_a_3857_);
                    v___x_3870_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3870_, 0, v___x_3868_);
                    crate::leanh::lean_ctor_set(v___x_3870_, 1, v___x_3869_);
                    v___x_3871_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9,
                    );
                    v___x_3872_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3872_, 0, v___x_3870_);
                    crate::leanh::lean_ctor_set(v___x_3872_, 1, v___x_3871_);
                    v___x_3873_ = l_Lean_indentExpr(v_a_3855_);
                    v___x_3874_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3874_, 0, v___x_3872_);
                    crate::leanh::lean_ctor_set(v___x_3874_, 1, v___x_3873_);
                    v___x_3875_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3874_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
                    crate::leanh::lean_dec_ref(v___y_3823_);
                    return v___x_3875_;
                } else {
                    crate::leanh::lean_dec(v_a_3857_);
                    crate::leanh::lean_dec(v_a_3855_);
                    crate::leanh::lean_dec_ref(v___y_3823_);
                    crate::leanh::lean_dec(v___x_3802_);
                    v___x_3876_ = crate::leanh::lean_box(0);
                    if v_isShared_3862_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3861_, 0, v___x_3876_);
                        v___x_3878_ = v___x_3861_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
                        v___x_3878_ = v_reuseFailAlloc_3879_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_3878_;
            }
            6 => {
                if v_isShared_3884_ == 0 {
                    v___x_3886_ = v___x_3883_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
                    v___x_3886_ = v_reuseFailAlloc_3887_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3886_;
            }
            8 => {
                if v_isShared_3892_ == 0 {
                    v___x_3894_ = v___x_3891_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3894_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_c_3806_) == 1 {
                    if crate::leanh::lean_obj_tag(v_ty_3807_) == 1 {
                        v_val_3910_ = crate::leanh::lean_ctor_get(v_c_3806_, 0);
                        crate::leanh::lean_inc(v_val_3910_);
                        crate::leanh::lean_dec_ref_known(v_c_3806_, 1);
                        v_val_3911_ = crate::leanh::lean_ctor_get(v_ty_3807_, 0);
                        crate::leanh::lean_inc(v_val_3911_);
                        crate::leanh::lean_dec_ref_known(v_ty_3807_, 1);
                        v___x_3912_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_3910_);
                        if crate::leanh::lean_obj_tag(v___x_3912_) == 1 {
                            v_val_3913_ = crate::leanh::lean_ctor_get(v___x_3912_, 0);
                            crate::leanh::lean_inc(v_val_3913_);
                            crate::leanh::lean_dec_ref_known(v___x_3912_, 1);
                            v___x_3914_ = crate::leanh::lean_box(0);
                            v___x_3915_ = l_Lean_Elab_Tactic_elabTerm(
                                v_val_3911_,
                                v___x_3914_,
                                v___x_3803_,
                                v___y_3902_,
                                v___y_3903_,
                                v___y_3904_,
                                v___y_3905_,
                                v___y_3906_,
                                v___y_3907_,
                                v___y_3908_,
                                v___y_3909_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3915_) == 0 {
                                v_a_3916_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                                crate::leanh::lean_inc_n(v_a_3916_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_3915_, 1);
                                v___x_3917_ = l_Lean_LocalDecl_type(v_lDecl_3901_);
                                v___x_3918_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_3917_, v___y_3907_);
                                v_a_3919_ = crate::leanh::lean_ctor_get(v___x_3918_, 0);
                                crate::leanh::lean_inc_n(v_a_3919_, 2);
                                crate::leanh::lean_dec_ref(v___x_3918_);
                                v___x_3920_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                                    v_a_3916_,
                                    v_a_3919_,
                                    v_val_3913_,
                                    v___y_3906_,
                                    v___y_3907_,
                                    v___y_3908_,
                                    v___y_3909_,
                                );
                                crate::leanh::lean_dec(v_val_3913_);
                                if crate::leanh::lean_obj_tag(v___x_3920_) == 0 {
                                    v_a_3921_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
                                    crate::leanh::lean_inc(v_a_3921_);
                                    crate::leanh::lean_dec_ref_known(v___x_3920_, 1);
                                    v___x_3922_ = (crate::leanh::lean_unbox(v_a_3921_) as u8);
                                    crate::leanh::lean_dec(v_a_3921_);
                                    if v___x_3922_ == 0 {
                                        crate::leanh::lean_dec_ref(v_lDecl_3901_);
                                        crate::leanh::lean_dec(v_eq_3805_);
                                        crate::leanh::lean_dec(v_val_3804_);
                                        v___x_3923_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
                                        v___x_3924_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                                        v___x_3925_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3925_, 0, v___x_3923_);
                                        crate::leanh::lean_ctor_set(v___x_3925_, 1, v___x_3924_);
                                        v___x_3926_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
                                        v___x_3927_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3927_, 0, v___x_3925_);
                                        crate::leanh::lean_ctor_set(v___x_3927_, 1, v___x_3926_);
                                        v___x_3928_ = l_Lean_indentExpr(v_a_3919_);
                                        v___x_3929_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3929_, 0, v___x_3927_);
                                        crate::leanh::lean_ctor_set(v___x_3929_, 1, v___x_3928_);
                                        v___x_3930_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
                                        v___x_3931_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3931_, 0, v___x_3929_);
                                        crate::leanh::lean_ctor_set(v___x_3931_, 1, v___x_3930_);
                                        v___x_3932_ = l_Lean_indentExpr(v_a_3916_);
                                        v___x_3933_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3933_, 0, v___x_3931_);
                                        crate::leanh::lean_ctor_set(v___x_3933_, 1, v___x_3932_);
                                        v___x_3934_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3933_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
                                        crate::leanh::lean_dec_ref(v___y_3906_);
                                        return v___x_3934_;
                                    } else {
                                        crate::leanh::lean_dec(v_a_3919_);
                                        crate::leanh::lean_dec(v_a_3916_);
                                        v___y_3818_ = v_lDecl_3901_;
                                        v___y_3819_ = v___y_3902_;
                                        v___y_3820_ = v___y_3903_;
                                        v___y_3821_ = v___y_3904_;
                                        v___y_3822_ = v___y_3905_;
                                        v___y_3823_ = v___y_3906_;
                                        v___y_3824_ = v___y_3907_;
                                        v___y_3825_ = v___y_3908_;
                                        v___y_3826_ = v___y_3909_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3919_);
                                    crate::leanh::lean_dec(v_a_3916_);
                                    crate::leanh::lean_dec_ref(v___y_3906_);
                                    crate::leanh::lean_dec_ref(v_lDecl_3901_);
                                    crate::leanh::lean_dec(v_eq_3805_);
                                    crate::leanh::lean_dec(v_val_3804_);
                                    crate::leanh::lean_dec(v___x_3802_);
                                    v_a_3935_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
                                    v_isSharedCheck_3942_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3920_)) as u8;
                                    if v_isSharedCheck_3942_ == 0 {
                                        v___x_3937_ = v___x_3920_;
                                        v_isShared_3938_ = v_isSharedCheck_3942_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3935_);
                                        crate::leanh::lean_dec(v___x_3920_);
                                        v___x_3937_ = crate::leanh::lean_box(0);
                                        v_isShared_3938_ = v_isSharedCheck_3942_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_3913_);
                                crate::leanh::lean_dec_ref(v___y_3906_);
                                crate::leanh::lean_dec_ref(v_lDecl_3901_);
                                crate::leanh::lean_dec(v_eq_3805_);
                                crate::leanh::lean_dec(v_val_3804_);
                                crate::leanh::lean_dec(v___x_3802_);
                                v_a_3943_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                                v_isSharedCheck_3950_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3915_)) as u8;
                                if v_isSharedCheck_3950_ == 0 {
                                    v___x_3945_ = v___x_3915_;
                                    v_isShared_3946_ = v_isSharedCheck_3950_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3943_);
                                    crate::leanh::lean_dec(v___x_3915_);
                                    v___x_3945_ = crate::leanh::lean_box(0);
                                    v_isShared_3946_ = v_isSharedCheck_3950_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3912_);
                            crate::leanh::lean_dec(v_val_3911_);
                            crate::leanh::lean_dec_ref(v___y_3906_);
                            crate::leanh::lean_dec_ref(v_lDecl_3901_);
                            crate::leanh::lean_dec(v_eq_3805_);
                            crate::leanh::lean_dec(v_val_3804_);
                            crate::leanh::lean_dec(v___x_3802_);
                            v___x_3951_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_3951_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_c_3806_, 1);
                        crate::leanh::lean_dec(v_ty_3807_);
                        v___y_3818_ = v_lDecl_3901_;
                        v___y_3819_ = v___y_3902_;
                        v___y_3820_ = v___y_3903_;
                        v___y_3821_ = v___y_3904_;
                        v___y_3822_ = v___y_3905_;
                        v___y_3823_ = v___y_3906_;
                        v___y_3824_ = v___y_3907_;
                        v___y_3825_ = v___y_3908_;
                        v___y_3826_ = v___y_3909_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ty_3807_);
                    crate::leanh::lean_dec(v_c_3806_);
                    v___y_3818_ = v_lDecl_3901_;
                    v___y_3819_ = v___y_3902_;
                    v___y_3820_ = v___y_3903_;
                    v___y_3821_ = v___y_3904_;
                    v___y_3822_ = v___y_3905_;
                    v___y_3823_ = v___y_3906_;
                    v___y_3824_ = v___y_3907_;
                    v___y_3825_ = v___y_3908_;
                    v___y_3826_ = v___y_3909_;
                    state = 1;
                    continue;
                }
            }
            11 => {
                if v_isShared_3938_ == 0 {
                    v___x_3940_ = v___x_3937_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
                    v___x_3940_ = v_reuseFailAlloc_3941_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3940_;
            }
            13 => {
                if v_isShared_3946_ == 0 {
                    v___x_3948_ = v___x_3945_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
                    v___x_3948_ = v_reuseFailAlloc_3949_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3948_;
            }
            15 => {
                if v_isShared_3965_ == 0 {
                    v___x_3967_ = v___x_3964_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
                    v___x_3967_ = v_reuseFailAlloc_3968_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3967_;
            }
            17 => {
                if v_isShared_3974_ == 0 {
                    v___x_3976_ = v___x_3973_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3976_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed(
    mut v___x_3979_: *mut crate::leanh::LeanObject,
    mut v___x_3980_: *mut crate::leanh::LeanObject,
    mut v_val_3981_: *mut crate::leanh::LeanObject,
    mut v_eq_3982_: *mut crate::leanh::LeanObject,
    mut v_c_3983_: *mut crate::leanh::LeanObject,
    mut v_ty_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
    mut v___y_3989_: *mut crate::leanh::LeanObject,
    mut v___y_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_14521__boxed_3994_: u8 = 0;
    let mut v_res_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_14521__boxed_3994_ = (crate::leanh::lean_unbox(v___x_3980_) as u8);
    v_res_3995_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(
        v___x_3979_,
        v___x_14521__boxed_3994_,
        v_val_3981_,
        v_eq_3982_,
        v_c_3983_,
        v_ty_3984_,
        v___y_3985_,
        v___y_3986_,
        v___y_3987_,
        v___y_3988_,
        v___y_3989_,
        v___y_3990_,
        v___y_3991_,
        v___y_3992_,
    );
    crate::leanh::lean_dec(v___y_3992_);
    crate::leanh::lean_dec_ref(v___y_3991_);
    crate::leanh::lean_dec(v___y_3990_);
    crate::leanh::lean_dec(v___y_3988_);
    crate::leanh::lean_dec_ref(v___y_3987_);
    crate::leanh::lean_dec(v___y_3986_);
    crate::leanh::lean_dec_ref(v___y_3985_);
    return v_res_3995_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(
    mut v___x_3996_: *mut crate::leanh::LeanObject,
    mut v_val_3997_: *mut crate::leanh::LeanObject,
    mut v_eq_3998_: *mut crate::leanh::LeanObject,
    mut v_c_3999_: *mut crate::leanh::LeanObject,
    mut v_ty_4000_: *mut crate::leanh::LeanObject,
    mut v___y_4001_: *mut crate::leanh::LeanObject,
    mut v___y_4002_: *mut crate::leanh::LeanObject,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v___x_4057_: u8 = 0;
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut v_a_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_a_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut v_reuseFailAlloc_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecl_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: u8 = 0;
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_a_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4145_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_val_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_3996_);
                v___x_4147_ = l_Lean_Elab_Tactic_getFVarId(
                    v___x_3996_,
                    v___y_4001_,
                    v___y_4002_,
                    v___y_4003_,
                    v___y_4004_,
                    v___y_4005_,
                    v___y_4006_,
                    v___y_4007_,
                    v___y_4008_,
                );
                if crate::leanh::lean_obj_tag(v___x_4147_) == 0 {
                    v_a_4148_ = crate::leanh::lean_ctor_get(v___x_4147_, 0);
                    crate::leanh::lean_inc(v_a_4148_);
                    crate::leanh::lean_dec_ref_known(v___x_4147_, 1);
                    v_lctx_4149_ = crate::leanh::lean_ctor_get(v___y_4005_, 2);
                    crate::leanh::lean_inc_ref(v_lctx_4149_);
                    v___x_4150_ = lean_local_ctx_find(v_lctx_4149_, v_a_4148_);
                    if crate::leanh::lean_obj_tag(v___x_4150_) == 0 {
                        crate::leanh::lean_dec(v_ty_4000_);
                        crate::leanh::lean_dec(v_c_3999_);
                        crate::leanh::lean_dec(v_eq_3998_);
                        crate::leanh::lean_dec(v_val_3997_);
                        v___x_4151_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                        );
                        v___x_4152_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                        v___x_4153_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4153_, 0, v___x_4151_);
                        crate::leanh::lean_ctor_set(v___x_4153_, 1, v___x_4152_);
                        v___x_4154_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
                        v___x_4155_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4155_, 0, v___x_4153_);
                        crate::leanh::lean_ctor_set(v___x_4155_, 1, v___x_4154_);
                        v___x_4156_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4155_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
                        crate::leanh::lean_dec_ref(v___y_4005_);
                        v_a_4157_ = crate::leanh::lean_ctor_get(v___x_4156_, 0);
                        v_isSharedCheck_4164_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4156_)) as u8;
                        if v_isSharedCheck_4164_ == 0 {
                            v___x_4159_ = v___x_4156_;
                            v_isShared_4160_ = v_isSharedCheck_4164_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4157_);
                            crate::leanh::lean_dec(v___x_4156_);
                            v___x_4159_ = crate::leanh::lean_box(0);
                            v_isShared_4160_ = v_isSharedCheck_4164_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v_val_4165_ = crate::leanh::lean_ctor_get(v___x_4150_, 0);
                        crate::leanh::lean_inc(v_val_4165_);
                        crate::leanh::lean_dec_ref_known(v___x_4150_, 1);
                        v_lDecl_4095_ = v_val_4165_;
                        v___y_4096_ = v___y_4001_;
                        v___y_4097_ = v___y_4002_;
                        v___y_4098_ = v___y_4003_;
                        v___y_4099_ = v___y_4004_;
                        v___y_4100_ = v___y_4005_;
                        v___y_4101_ = v___y_4006_;
                        v___y_4102_ = v___y_4007_;
                        v___y_4103_ = v___y_4008_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4005_);
                    crate::leanh::lean_dec(v_ty_4000_);
                    crate::leanh::lean_dec(v_c_3999_);
                    crate::leanh::lean_dec(v_eq_3998_);
                    crate::leanh::lean_dec(v_val_3997_);
                    crate::leanh::lean_dec(v___x_3996_);
                    v_a_4166_ = crate::leanh::lean_ctor_get(v___x_4147_, 0);
                    v_isSharedCheck_4173_ = (!crate::leanh::lean_is_exclusive(v___x_4147_)) as u8;
                    if v_isSharedCheck_4173_ == 0 {
                        v___x_4168_ = v___x_4147_;
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4166_);
                        crate::leanh::lean_dec(v___x_4147_);
                        v___x_4168_ = crate::leanh::lean_box(0);
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4020_ = 0;
                v___x_4021_ = l_Lean_LocalDecl_value_x3f(v___y_4011_, v___x_4020_);
                if crate::leanh::lean_obj_tag(v___x_4021_) == 0 {
                    crate::leanh::lean_dec_ref(v___y_4011_);
                    crate::leanh::lean_dec(v_eq_3998_);
                    if crate::leanh::lean_obj_tag(v_val_3997_) == 0 {
                        crate::leanh::lean_dec_ref(v___y_4016_);
                        crate::leanh::lean_dec(v___x_3996_);
                        v___x_4022_ = crate::leanh::lean_box(0);
                        v___x_4023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4023_, 0, v___x_4022_);
                        return v___x_4023_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_val_3997_, 1);
                        v___x_4024_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_4025_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                        v___x_4026_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4026_, 0, v___x_4024_);
                        crate::leanh::lean_ctor_set(v___x_4026_, 1, v___x_4025_);
                        v___x_4027_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1,
                        );
                        v___x_4028_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4028_, 0, v___x_4026_);
                        crate::leanh::lean_ctor_set(v___x_4028_, 1, v___x_4027_);
                        v___x_4029_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4028_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
                        crate::leanh::lean_dec_ref(v___y_4016_);
                        return v___x_4029_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_val_3997_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4021_, 1);
                        crate::leanh::lean_dec_ref(v___y_4011_);
                        crate::leanh::lean_dec(v_eq_3998_);
                        v___x_4030_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_4031_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                        v___x_4032_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4032_, 0, v___x_4030_);
                        crate::leanh::lean_ctor_set(v___x_4032_, 1, v___x_4031_);
                        v___x_4033_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3,
                        );
                        v___x_4034_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4034_, 0, v___x_4032_);
                        crate::leanh::lean_ctor_set(v___x_4034_, 1, v___x_4033_);
                        v___x_4035_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4034_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
                        crate::leanh::lean_dec_ref(v___y_4016_);
                        return v___x_4035_;
                    } else {
                        if crate::leanh::lean_obj_tag(v_eq_3998_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_val_3997_, 1);
                            crate::leanh::lean_dec_ref_known(v___x_4021_, 1);
                            crate::leanh::lean_dec_ref(v___y_4016_);
                            crate::leanh::lean_dec_ref(v___y_4011_);
                            crate::leanh::lean_dec(v___x_3996_);
                            v___x_4036_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_4036_;
                        } else {
                            v_val_4037_ = crate::leanh::lean_ctor_get(v___x_4021_, 0);
                            crate::leanh::lean_inc(v_val_4037_);
                            crate::leanh::lean_dec_ref_known(v___x_4021_, 1);
                            v_val_4038_ = crate::leanh::lean_ctor_get(v_val_3997_, 0);
                            crate::leanh::lean_inc(v_val_4038_);
                            crate::leanh::lean_dec_ref_known(v_val_3997_, 1);
                            v_val_4039_ = crate::leanh::lean_ctor_get(v_eq_3998_, 0);
                            crate::leanh::lean_inc(v_val_4039_);
                            crate::leanh::lean_dec_ref_known(v_eq_3998_, 1);
                            v___x_4040_ =
                                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_4039_);
                            if crate::leanh::lean_obj_tag(v___x_4040_) == 1 {
                                v_val_4041_ = crate::leanh::lean_ctor_get(v___x_4040_, 0);
                                v_isSharedCheck_4092_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4040_)) as u8;
                                if v_isSharedCheck_4092_ == 0 {
                                    v___x_4043_ = v___x_4040_;
                                    v_isShared_4044_ = v_isSharedCheck_4092_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_4041_);
                                    crate::leanh::lean_dec(v___x_4040_);
                                    v___x_4043_ = crate::leanh::lean_box(0);
                                    v_isShared_4044_ = v_isSharedCheck_4092_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_4040_);
                                crate::leanh::lean_dec(v_val_4038_);
                                crate::leanh::lean_dec(v_val_4037_);
                                crate::leanh::lean_dec_ref(v___y_4016_);
                                crate::leanh::lean_dec_ref(v___y_4011_);
                                crate::leanh::lean_dec(v___x_3996_);
                                v___x_4093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                                return v___x_4093_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4045_ = l_Lean_LocalDecl_type(v___y_4011_);
                crate::leanh::lean_dec_ref(v___y_4011_);
                if v_isShared_4044_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4043_, 0, v___x_4045_);
                    v___x_4047_ = v___x_4043_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4045_);
                    v___x_4047_ = v_reuseFailAlloc_4091_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4048_ = l_Lean_Elab_Tactic_elabTerm(
                    v_val_4038_,
                    v___x_4047_,
                    v___x_4020_,
                    v___y_4012_,
                    v___y_4013_,
                    v___y_4014_,
                    v___y_4015_,
                    v___y_4016_,
                    v___y_4017_,
                    v___y_4018_,
                    v___y_4019_,
                );
                if crate::leanh::lean_obj_tag(v___x_4048_) == 0 {
                    v_a_4049_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                    crate::leanh::lean_inc_n(v_a_4049_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4048_, 1);
                    v___x_4050_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_4037_, v___y_4017_);
                    v_a_4051_ = crate::leanh::lean_ctor_get(v___x_4050_, 0);
                    crate::leanh::lean_inc_n(v_a_4051_, 2);
                    crate::leanh::lean_dec_ref(v___x_4050_);
                    v___x_4052_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                        v_a_4049_,
                        v_a_4051_,
                        v_val_4041_,
                        v___y_4016_,
                        v___y_4017_,
                        v___y_4018_,
                        v___y_4019_,
                    );
                    crate::leanh::lean_dec(v_val_4041_);
                    if crate::leanh::lean_obj_tag(v___x_4052_) == 0 {
                        v_a_4053_ = crate::leanh::lean_ctor_get(v___x_4052_, 0);
                        v_isSharedCheck_4074_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4052_)) as u8;
                        if v_isSharedCheck_4074_ == 0 {
                            v___x_4055_ = v___x_4052_;
                            v_isShared_4056_ = v_isSharedCheck_4074_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4053_);
                            crate::leanh::lean_dec(v___x_4052_);
                            v___x_4055_ = crate::leanh::lean_box(0);
                            v_isShared_4056_ = v_isSharedCheck_4074_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4051_);
                        crate::leanh::lean_dec(v_a_4049_);
                        crate::leanh::lean_dec_ref(v___y_4016_);
                        crate::leanh::lean_dec(v___x_3996_);
                        v_a_4075_ = crate::leanh::lean_ctor_get(v___x_4052_, 0);
                        v_isSharedCheck_4082_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4052_)) as u8;
                        if v_isSharedCheck_4082_ == 0 {
                            v___x_4077_ = v___x_4052_;
                            v_isShared_4078_ = v_isSharedCheck_4082_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4075_);
                            crate::leanh::lean_dec(v___x_4052_);
                            v___x_4077_ = crate::leanh::lean_box(0);
                            v_isShared_4078_ = v_isSharedCheck_4082_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_val_4041_);
                    crate::leanh::lean_dec(v_val_4037_);
                    crate::leanh::lean_dec_ref(v___y_4016_);
                    crate::leanh::lean_dec(v___x_3996_);
                    v_a_4083_ = crate::leanh::lean_ctor_get(v___x_4048_, 0);
                    v_isSharedCheck_4090_ = (!crate::leanh::lean_is_exclusive(v___x_4048_)) as u8;
                    if v_isSharedCheck_4090_ == 0 {
                        v___x_4085_ = v___x_4048_;
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4083_);
                        crate::leanh::lean_dec(v___x_4048_);
                        v___x_4085_ = crate::leanh::lean_box(0);
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4057_ = (crate::leanh::lean_unbox(v_a_4053_) as u8);
                crate::leanh::lean_dec(v_a_4053_);
                if v___x_4057_ == 0 {
                    crate::leanh::lean_del_object(v___x_4055_);
                    v___x_4058_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                    );
                    v___x_4059_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                    v___x_4060_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4060_, 0, v___x_4058_);
                    crate::leanh::lean_ctor_set(v___x_4060_, 1, v___x_4059_);
                    v___x_4061_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7,
                    );
                    v___x_4062_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4062_, 0, v___x_4060_);
                    crate::leanh::lean_ctor_set(v___x_4062_, 1, v___x_4061_);
                    v___x_4063_ = l_Lean_indentExpr(v_a_4051_);
                    v___x_4064_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4064_, 0, v___x_4062_);
                    crate::leanh::lean_ctor_set(v___x_4064_, 1, v___x_4063_);
                    v___x_4065_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9,
                    );
                    v___x_4066_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4066_, 0, v___x_4064_);
                    crate::leanh::lean_ctor_set(v___x_4066_, 1, v___x_4065_);
                    v___x_4067_ = l_Lean_indentExpr(v_a_4049_);
                    v___x_4068_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4068_, 0, v___x_4066_);
                    crate::leanh::lean_ctor_set(v___x_4068_, 1, v___x_4067_);
                    v___x_4069_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4068_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
                    crate::leanh::lean_dec_ref(v___y_4016_);
                    return v___x_4069_;
                } else {
                    crate::leanh::lean_dec(v_a_4051_);
                    crate::leanh::lean_dec(v_a_4049_);
                    crate::leanh::lean_dec_ref(v___y_4016_);
                    crate::leanh::lean_dec(v___x_3996_);
                    v___x_4070_ = crate::leanh::lean_box(0);
                    if v_isShared_4056_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4055_, 0, v___x_4070_);
                        v___x_4072_ = v___x_4055_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4070_);
                        v___x_4072_ = v_reuseFailAlloc_4073_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4072_;
            }
            6 => {
                if v_isShared_4078_ == 0 {
                    v___x_4080_ = v___x_4077_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4081_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
                    v___x_4080_ = v_reuseFailAlloc_4081_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4080_;
            }
            8 => {
                if v_isShared_4086_ == 0 {
                    v___x_4088_ = v___x_4085_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
                    v___x_4088_ = v_reuseFailAlloc_4089_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4088_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v_c_3999_) == 1 {
                    if crate::leanh::lean_obj_tag(v_ty_4000_) == 1 {
                        v_val_4104_ = crate::leanh::lean_ctor_get(v_c_3999_, 0);
                        crate::leanh::lean_inc(v_val_4104_);
                        crate::leanh::lean_dec_ref_known(v_c_3999_, 1);
                        v_val_4105_ = crate::leanh::lean_ctor_get(v_ty_4000_, 0);
                        crate::leanh::lean_inc(v_val_4105_);
                        crate::leanh::lean_dec_ref_known(v_ty_4000_, 1);
                        v___x_4106_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_4104_);
                        if crate::leanh::lean_obj_tag(v___x_4106_) == 1 {
                            v_val_4107_ = crate::leanh::lean_ctor_get(v___x_4106_, 0);
                            crate::leanh::lean_inc(v_val_4107_);
                            crate::leanh::lean_dec_ref_known(v___x_4106_, 1);
                            v___x_4108_ = crate::leanh::lean_box(0);
                            v___x_4109_ = 0;
                            v___x_4110_ = l_Lean_Elab_Tactic_elabTerm(
                                v_val_4105_,
                                v___x_4108_,
                                v___x_4109_,
                                v___y_4096_,
                                v___y_4097_,
                                v___y_4098_,
                                v___y_4099_,
                                v___y_4100_,
                                v___y_4101_,
                                v___y_4102_,
                                v___y_4103_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4110_) == 0 {
                                v_a_4111_ = crate::leanh::lean_ctor_get(v___x_4110_, 0);
                                crate::leanh::lean_inc_n(v_a_4111_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_4110_, 1);
                                v___x_4112_ = l_Lean_LocalDecl_type(v_lDecl_4095_);
                                v___x_4113_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_4112_, v___y_4101_);
                                v_a_4114_ = crate::leanh::lean_ctor_get(v___x_4113_, 0);
                                crate::leanh::lean_inc_n(v_a_4114_, 2);
                                crate::leanh::lean_dec_ref(v___x_4113_);
                                v___x_4115_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                                    v_a_4111_,
                                    v_a_4114_,
                                    v_val_4107_,
                                    v___y_4100_,
                                    v___y_4101_,
                                    v___y_4102_,
                                    v___y_4103_,
                                );
                                crate::leanh::lean_dec(v_val_4107_);
                                if crate::leanh::lean_obj_tag(v___x_4115_) == 0 {
                                    v_a_4116_ = crate::leanh::lean_ctor_get(v___x_4115_, 0);
                                    crate::leanh::lean_inc(v_a_4116_);
                                    crate::leanh::lean_dec_ref_known(v___x_4115_, 1);
                                    v___x_4117_ = (crate::leanh::lean_unbox(v_a_4116_) as u8);
                                    crate::leanh::lean_dec(v_a_4116_);
                                    if v___x_4117_ == 0 {
                                        crate::leanh::lean_dec_ref(v_lDecl_4095_);
                                        crate::leanh::lean_dec(v_eq_3998_);
                                        crate::leanh::lean_dec(v_val_3997_);
                                        v___x_4118_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
                                        v___x_4119_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                                        v___x_4120_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4120_, 0, v___x_4118_);
                                        crate::leanh::lean_ctor_set(v___x_4120_, 1, v___x_4119_);
                                        v___x_4121_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
                                        v___x_4122_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4122_, 0, v___x_4120_);
                                        crate::leanh::lean_ctor_set(v___x_4122_, 1, v___x_4121_);
                                        v___x_4123_ = l_Lean_indentExpr(v_a_4114_);
                                        v___x_4124_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4124_, 0, v___x_4122_);
                                        crate::leanh::lean_ctor_set(v___x_4124_, 1, v___x_4123_);
                                        v___x_4125_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
                                        v___x_4126_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4126_, 0, v___x_4124_);
                                        crate::leanh::lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                                        v___x_4127_ = l_Lean_indentExpr(v_a_4111_);
                                        v___x_4128_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4128_, 0, v___x_4126_);
                                        crate::leanh::lean_ctor_set(v___x_4128_, 1, v___x_4127_);
                                        v___x_4129_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4128_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
                                        crate::leanh::lean_dec_ref(v___y_4100_);
                                        return v___x_4129_;
                                    } else {
                                        crate::leanh::lean_dec(v_a_4114_);
                                        crate::leanh::lean_dec(v_a_4111_);
                                        v___y_4011_ = v_lDecl_4095_;
                                        v___y_4012_ = v___y_4096_;
                                        v___y_4013_ = v___y_4097_;
                                        v___y_4014_ = v___y_4098_;
                                        v___y_4015_ = v___y_4099_;
                                        v___y_4016_ = v___y_4100_;
                                        v___y_4017_ = v___y_4101_;
                                        v___y_4018_ = v___y_4102_;
                                        v___y_4019_ = v___y_4103_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4114_);
                                    crate::leanh::lean_dec(v_a_4111_);
                                    crate::leanh::lean_dec_ref(v___y_4100_);
                                    crate::leanh::lean_dec_ref(v_lDecl_4095_);
                                    crate::leanh::lean_dec(v_eq_3998_);
                                    crate::leanh::lean_dec(v_val_3997_);
                                    crate::leanh::lean_dec(v___x_3996_);
                                    v_a_4130_ = crate::leanh::lean_ctor_get(v___x_4115_, 0);
                                    v_isSharedCheck_4137_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4115_)) as u8;
                                    if v_isSharedCheck_4137_ == 0 {
                                        v___x_4132_ = v___x_4115_;
                                        v_isShared_4133_ = v_isSharedCheck_4137_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4130_);
                                        crate::leanh::lean_dec(v___x_4115_);
                                        v___x_4132_ = crate::leanh::lean_box(0);
                                        v_isShared_4133_ = v_isSharedCheck_4137_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_4107_);
                                crate::leanh::lean_dec_ref(v___y_4100_);
                                crate::leanh::lean_dec_ref(v_lDecl_4095_);
                                crate::leanh::lean_dec(v_eq_3998_);
                                crate::leanh::lean_dec(v_val_3997_);
                                crate::leanh::lean_dec(v___x_3996_);
                                v_a_4138_ = crate::leanh::lean_ctor_get(v___x_4110_, 0);
                                v_isSharedCheck_4145_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4110_)) as u8;
                                if v_isSharedCheck_4145_ == 0 {
                                    v___x_4140_ = v___x_4110_;
                                    v_isShared_4141_ = v_isSharedCheck_4145_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4138_);
                                    crate::leanh::lean_dec(v___x_4110_);
                                    v___x_4140_ = crate::leanh::lean_box(0);
                                    v_isShared_4141_ = v_isSharedCheck_4145_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4106_);
                            crate::leanh::lean_dec(v_val_4105_);
                            crate::leanh::lean_dec_ref(v___y_4100_);
                            crate::leanh::lean_dec_ref(v_lDecl_4095_);
                            crate::leanh::lean_dec(v_eq_3998_);
                            crate::leanh::lean_dec(v_val_3997_);
                            crate::leanh::lean_dec(v___x_3996_);
                            v___x_4146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_4146_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_c_3999_, 1);
                        crate::leanh::lean_dec(v_ty_4000_);
                        v___y_4011_ = v_lDecl_4095_;
                        v___y_4012_ = v___y_4096_;
                        v___y_4013_ = v___y_4097_;
                        v___y_4014_ = v___y_4098_;
                        v___y_4015_ = v___y_4099_;
                        v___y_4016_ = v___y_4100_;
                        v___y_4017_ = v___y_4101_;
                        v___y_4018_ = v___y_4102_;
                        v___y_4019_ = v___y_4103_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ty_4000_);
                    crate::leanh::lean_dec(v_c_3999_);
                    v___y_4011_ = v_lDecl_4095_;
                    v___y_4012_ = v___y_4096_;
                    v___y_4013_ = v___y_4097_;
                    v___y_4014_ = v___y_4098_;
                    v___y_4015_ = v___y_4099_;
                    v___y_4016_ = v___y_4100_;
                    v___y_4017_ = v___y_4101_;
                    v___y_4018_ = v___y_4102_;
                    v___y_4019_ = v___y_4103_;
                    state = 1;
                    continue;
                }
            }
            11 => {
                if v_isShared_4133_ == 0 {
                    v___x_4135_ = v___x_4132_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
                    v___x_4135_ = v_reuseFailAlloc_4136_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4135_;
            }
            13 => {
                if v_isShared_4141_ == 0 {
                    v___x_4143_ = v___x_4140_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
                    v___x_4143_ = v_reuseFailAlloc_4144_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4143_;
            }
            15 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4162_;
            }
            17 => {
                if v_isShared_4169_ == 0 {
                    v___x_4171_ = v___x_4168_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
                    v___x_4171_ = v_reuseFailAlloc_4172_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed(
    mut v___x_4174_: *mut crate::leanh::LeanObject,
    mut v_val_4175_: *mut crate::leanh::LeanObject,
    mut v_eq_4176_: *mut crate::leanh::LeanObject,
    mut v_c_4177_: *mut crate::leanh::LeanObject,
    mut v_ty_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(
        v___x_4174_,
        v_val_4175_,
        v_eq_4176_,
        v_c_4177_,
        v_ty_4178_,
        v___y_4179_,
        v___y_4180_,
        v___y_4181_,
        v___y_4182_,
        v___y_4183_,
        v___y_4184_,
        v___y_4185_,
        v___y_4186_,
    );
    crate::leanh::lean_dec(v___y_4186_);
    crate::leanh::lean_dec_ref(v___y_4185_);
    crate::leanh::lean_dec(v___y_4184_);
    crate::leanh::lean_dec(v___y_4182_);
    crate::leanh::lean_dec_ref(v___y_4181_);
    crate::leanh::lean_dec(v___y_4180_);
    crate::leanh::lean_dec_ref(v___y_4179_);
    return v_res_4188_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(
    mut v_x_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
    mut v_a_4205_: *mut crate::leanh::LeanObject,
    mut v_a_4206_: *mut crate::leanh::LeanObject,
    mut v_a_4207_: *mut crate::leanh::LeanObject,
    mut v_a_4208_: *mut crate::leanh::LeanObject,
    mut v_a_4209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: u8 = 0;
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: u8 = 0;
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: u8 = 0;
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u8 = 0;
    let mut v___x_4299_: u8 = 0;
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ty_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4211_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
                crate::leanh::lean_inc(v_x_4201_);
                v___x_4212_ = l_Lean_Syntax_isOfKind(v_x_4201_, v___x_4211_);
                if v___x_4212_ == 0 {
                    v___x_4213_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3;
                    crate::leanh::lean_inc(v_x_4201_);
                    v___x_4214_ = l_Lean_Syntax_isOfKind(v_x_4201_, v___x_4213_);
                    if v___x_4214_ == 0 {
                        crate::leanh::lean_dec(v_x_4201_);
                        v___x_4215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_4215_;
                    } else {
                        v___x_4216_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4217_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4218_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4217_);
                        v___x_4235_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_4257_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4235_);
                        v___x_4258_ = l_Lean_Syntax_isNone(v___x_4257_);
                        if v___x_4258_ == 0 {
                            crate::leanh::lean_inc(v___x_4257_);
                            v___x_4259_ = l_Lean_Syntax_matchesNull(v___x_4257_, v___x_4235_);
                            if v___x_4259_ == 0 {
                                crate::leanh::lean_dec(v___x_4257_);
                                crate::leanh::lean_dec(v___x_4218_);
                                crate::leanh::lean_dec(v_x_4201_);
                                v___x_4260_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                                return v___x_4260_;
                            } else {
                                v_c_4261_ = l_Lean_Syntax_getArg(v___x_4257_, v___x_4216_);
                                v_ty_4262_ = l_Lean_Syntax_getArg(v___x_4257_, v___x_4217_);
                                crate::leanh::lean_dec(v___x_4257_);
                                v___x_4263_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4263_, 0, v_c_4261_);
                                v___x_4264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4264_, 0, v_ty_4262_);
                                v_c_4237_ = v___x_4263_;
                                v_ty_4238_ = v___x_4264_;
                                v___y_4239_ = v_a_4202_;
                                v___y_4240_ = v_a_4203_;
                                v___y_4241_ = v_a_4204_;
                                v___y_4242_ = v_a_4205_;
                                v___y_4243_ = v_a_4206_;
                                v___y_4244_ = v_a_4207_;
                                v___y_4245_ = v_a_4208_;
                                v___y_4246_ = v_a_4209_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4257_);
                            v___x_4265_ = crate::leanh::lean_box(0);
                            v_c_4237_ = v___x_4265_;
                            v_ty_4238_ = v___x_4265_;
                            v___y_4239_ = v_a_4202_;
                            v___y_4240_ = v_a_4203_;
                            v___y_4241_ = v_a_4204_;
                            v___y_4242_ = v_a_4205_;
                            v___y_4243_ = v_a_4206_;
                            v___y_4244_ = v_a_4207_;
                            v___y_4245_ = v_a_4208_;
                            v___y_4246_ = v_a_4209_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_4266_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4267_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4268_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4267_);
                    v___x_4284_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_4306_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4284_);
                    v___x_4307_ = l_Lean_Syntax_isNone(v___x_4306_);
                    if v___x_4307_ == 0 {
                        crate::leanh::lean_inc(v___x_4306_);
                        v___x_4308_ = l_Lean_Syntax_matchesNull(v___x_4306_, v___x_4284_);
                        if v___x_4308_ == 0 {
                            crate::leanh::lean_dec(v___x_4306_);
                            crate::leanh::lean_dec(v___x_4268_);
                            crate::leanh::lean_dec(v_x_4201_);
                            v___x_4309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_4309_;
                        } else {
                            v_c_4310_ = l_Lean_Syntax_getArg(v___x_4306_, v___x_4266_);
                            v_ty_4311_ = l_Lean_Syntax_getArg(v___x_4306_, v___x_4267_);
                            crate::leanh::lean_dec(v___x_4306_);
                            v___x_4312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4312_, 0, v_c_4310_);
                            v___x_4313_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4313_, 0, v_ty_4311_);
                            v_c_4286_ = v___x_4312_;
                            v_ty_4287_ = v___x_4313_;
                            v___y_4288_ = v_a_4202_;
                            v___y_4289_ = v_a_4203_;
                            v___y_4290_ = v_a_4204_;
                            v___y_4291_ = v_a_4205_;
                            v___y_4292_ = v_a_4206_;
                            v___y_4293_ = v_a_4207_;
                            v___y_4294_ = v_a_4208_;
                            v___y_4295_ = v_a_4209_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4306_);
                        v___x_4314_ = crate::leanh::lean_box(0);
                        v_c_4286_ = v___x_4314_;
                        v_ty_4287_ = v___x_4314_;
                        v___y_4288_ = v_a_4202_;
                        v___y_4289_ = v_a_4203_;
                        v___y_4290_ = v_a_4204_;
                        v___y_4291_ = v_a_4205_;
                        v___y_4292_ = v_a_4206_;
                        v___y_4293_ = v_a_4207_;
                        v___y_4294_ = v_a_4208_;
                        v___y_4295_ = v_a_4209_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4232_ = crate::leanh::lean_box((v___x_4212_) as usize);
                v___f_4233_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed
                        as *mut core::ffi::c_void,
                    15,
                    6,
                );
                crate::leanh::lean_closure_set(v___f_4233_, 0, v___x_4218_);
                crate::leanh::lean_closure_set(v___f_4233_, 1, v___x_4232_);
                crate::leanh::lean_closure_set(v___f_4233_, 2, v_val_4231_);
                crate::leanh::lean_closure_set(v___f_4233_, 3, v_eq_4230_);
                crate::leanh::lean_closure_set(v___f_4233_, 4, v___y_4229_);
                crate::leanh::lean_closure_set(v___f_4233_, 5, v___y_4226_);
                v___x_4234_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_4233_,
                    v___y_4220_,
                    v___y_4227_,
                    v___y_4222_,
                    v___y_4228_,
                    v___y_4225_,
                    v___y_4221_,
                    v___y_4224_,
                    v___y_4223_,
                );
                return v___x_4234_;
            }
            2 => {
                v___x_4247_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4248_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4247_);
                crate::leanh::lean_dec(v_x_4201_);
                v___x_4249_ = l_Lean_Syntax_isNone(v___x_4248_);
                if v___x_4249_ == 0 {
                    crate::leanh::lean_inc(v___x_4248_);
                    v___x_4250_ = l_Lean_Syntax_matchesNull(v___x_4248_, v___x_4235_);
                    if v___x_4250_ == 0 {
                        crate::leanh::lean_dec(v___x_4248_);
                        crate::leanh::lean_dec(v_ty_4238_);
                        crate::leanh::lean_dec(v_c_4237_);
                        crate::leanh::lean_dec(v___x_4218_);
                        v___x_4251_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_4251_;
                    } else {
                        v_eq_4252_ = l_Lean_Syntax_getArg(v___x_4248_, v___x_4216_);
                        v_val_4253_ = l_Lean_Syntax_getArg(v___x_4248_, v___x_4217_);
                        crate::leanh::lean_dec(v___x_4248_);
                        v___x_4254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4254_, 0, v_eq_4252_);
                        v___x_4255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4255_, 0, v_val_4253_);
                        v___y_4220_ = v___y_4239_;
                        v___y_4221_ = v___y_4244_;
                        v___y_4222_ = v___y_4241_;
                        v___y_4223_ = v___y_4246_;
                        v___y_4224_ = v___y_4245_;
                        v___y_4225_ = v___y_4243_;
                        v___y_4226_ = v_ty_4238_;
                        v___y_4227_ = v___y_4240_;
                        v___y_4228_ = v___y_4242_;
                        v___y_4229_ = v_c_4237_;
                        v_eq_4230_ = v___x_4254_;
                        v_val_4231_ = v___x_4255_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4248_);
                    v___x_4256_ = crate::leanh::lean_box(0);
                    v___y_4220_ = v___y_4239_;
                    v___y_4221_ = v___y_4244_;
                    v___y_4222_ = v___y_4241_;
                    v___y_4223_ = v___y_4246_;
                    v___y_4224_ = v___y_4245_;
                    v___y_4225_ = v___y_4243_;
                    v___y_4226_ = v_ty_4238_;
                    v___y_4227_ = v___y_4240_;
                    v___y_4228_ = v___y_4242_;
                    v___y_4229_ = v_c_4237_;
                    v_eq_4230_ = v___x_4256_;
                    v_val_4231_ = v___x_4256_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___f_4282_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed
                        as *mut core::ffi::c_void,
                    14,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_4282_, 0, v___x_4268_);
                crate::leanh::lean_closure_set(v___f_4282_, 1, v_val_4281_);
                crate::leanh::lean_closure_set(v___f_4282_, 2, v_eq_4280_);
                crate::leanh::lean_closure_set(v___f_4282_, 3, v___y_4276_);
                crate::leanh::lean_closure_set(v___f_4282_, 4, v___y_4279_);
                v___x_4283_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_4282_,
                    v___y_4274_,
                    v___y_4278_,
                    v___y_4272_,
                    v___y_4273_,
                    v___y_4270_,
                    v___y_4275_,
                    v___y_4277_,
                    v___y_4271_,
                );
                return v___x_4283_;
            }
            4 => {
                v___x_4296_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4297_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4296_);
                crate::leanh::lean_dec(v_x_4201_);
                v___x_4298_ = l_Lean_Syntax_isNone(v___x_4297_);
                if v___x_4298_ == 0 {
                    crate::leanh::lean_inc(v___x_4297_);
                    v___x_4299_ = l_Lean_Syntax_matchesNull(v___x_4297_, v___x_4284_);
                    if v___x_4299_ == 0 {
                        crate::leanh::lean_dec(v___x_4297_);
                        crate::leanh::lean_dec(v_ty_4287_);
                        crate::leanh::lean_dec(v_c_4286_);
                        crate::leanh::lean_dec(v___x_4268_);
                        v___x_4300_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_4300_;
                    } else {
                        v_eq_4301_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_4266_);
                        v_val_4302_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_4267_);
                        crate::leanh::lean_dec(v___x_4297_);
                        v___x_4303_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4303_, 0, v_eq_4301_);
                        v___x_4304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4304_, 0, v_val_4302_);
                        v___y_4270_ = v___y_4292_;
                        v___y_4271_ = v___y_4295_;
                        v___y_4272_ = v___y_4290_;
                        v___y_4273_ = v___y_4291_;
                        v___y_4274_ = v___y_4288_;
                        v___y_4275_ = v___y_4293_;
                        v___y_4276_ = v_c_4286_;
                        v___y_4277_ = v___y_4294_;
                        v___y_4278_ = v___y_4289_;
                        v___y_4279_ = v_ty_4287_;
                        v_eq_4280_ = v___x_4303_;
                        v_val_4281_ = v___x_4304_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4297_);
                    v___x_4305_ = crate::leanh::lean_box(0);
                    v___y_4270_ = v___y_4292_;
                    v___y_4271_ = v___y_4295_;
                    v___y_4272_ = v___y_4290_;
                    v___y_4273_ = v___y_4291_;
                    v___y_4274_ = v___y_4288_;
                    v___y_4275_ = v___y_4293_;
                    v___y_4276_ = v_c_4286_;
                    v___y_4277_ = v___y_4294_;
                    v___y_4278_ = v___y_4289_;
                    v___y_4279_ = v_ty_4287_;
                    v_eq_4280_ = v___x_4305_;
                    v_val_4281_ = v___x_4305_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed(
    mut v_x_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
    mut v_a_4320_: *mut crate::leanh::LeanObject,
    mut v_a_4321_: *mut crate::leanh::LeanObject,
    mut v_a_4322_: *mut crate::leanh::LeanObject,
    mut v_a_4323_: *mut crate::leanh::LeanObject,
    mut v_a_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4325_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(
        v_x_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_,
        v_a_4323_,
    );
    crate::leanh::lean_dec(v_a_4323_);
    crate::leanh::lean_dec_ref(v_a_4322_);
    crate::leanh::lean_dec(v_a_4321_);
    crate::leanh::lean_dec_ref(v_a_4320_);
    crate::leanh::lean_dec(v_a_4319_);
    crate::leanh::lean_dec_ref(v_a_4318_);
    crate::leanh::lean_dec(v_a_4317_);
    crate::leanh::lean_dec_ref(v_a_4316_);
    return v_res_4325_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4334_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4335_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
    v___x_4336_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1;
    v___x_4337_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4338_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4334_,
        v___x_4335_,
        v___x_4336_,
        v___x_4337_,
    );
    return v___x_4338_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___boxed(
    mut v_a_4339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4340_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
    return v_res_4340_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4367_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1;
    v___x_4368_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6;
    v___x_4369_ = l_Lean_addBuiltinDeclarationRanges(v___x_4367_, v___x_4368_);
    return v___x_4369_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___boxed(
    mut v_a_4370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4371_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
    return v_res_4371_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
    mut v_a_4377_: *mut crate::leanh::LeanObject,
    mut v_a_4378_: *mut crate::leanh::LeanObject,
    mut v_a_4379_: *mut crate::leanh::LeanObject,
    mut v_a_4380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4382_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(
        v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_,
        v_a_4380_,
    );
    return v___x_4382_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_a_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_a_4391_: *mut crate::leanh::LeanObject,
    mut v_a_4392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4393_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(
        v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_,
        v_a_4391_,
    );
    crate::leanh::lean_dec(v_a_4391_);
    crate::leanh::lean_dec_ref(v_a_4390_);
    crate::leanh::lean_dec(v_a_4389_);
    crate::leanh::lean_dec_ref(v_a_4388_);
    crate::leanh::lean_dec(v_a_4387_);
    crate::leanh::lean_dec_ref(v_a_4386_);
    crate::leanh::lean_dec(v_a_4385_);
    crate::leanh::lean_dec_ref(v_a_4384_);
    return v_res_4393_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1()
-> *mut crate::leanh::LeanObject {
    let mut v___f_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4402_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4403_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4404_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3;
    v___x_4405_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1;
    v___x_4406_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4403_,
        v___x_4404_,
        v___x_4405_,
        v___f_4402_,
    );
    return v___x_4406_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___boxed(
    mut v_a_4407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4408_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
    return v_res_4408_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4435_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1;
    v___x_4436_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6;
    v___x_4437_ = l_Lean_addBuiltinDeclarationRanges(v___x_4435_, v___x_4436_);
    return v___x_4437_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___boxed(
    mut v_a_4438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4439_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
    return v_res_4439_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4441_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
    v___x_4442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4442_, 0, v___x_4441_);
    return v___x_4442_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg___boxed(
    mut v___y_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
    return v_res_4444_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(
    mut v_00_u03b1_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
    mut v___y_4447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4449_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
    return v___x_4449_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___boxed(
    mut v_00_u03b1_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
    mut v___y_4453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(v_00_u03b1_4450_, v___y_4451_, v___y_4452_);
    crate::leanh::lean_dec(v___y_4452_);
    crate::leanh::lean_dec_ref(v___y_4451_);
    return v_res_4454_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
    v___x_4457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4457_, 0, v___x_4456_);
    return v___x_4457_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg___boxed(
    mut v___y_4458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
    return v_res_4459_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(
    mut v_00_u03b1_4460_: *mut crate::leanh::LeanObject,
    mut v___y_4461_: *mut crate::leanh::LeanObject,
    mut v___y_4462_: *mut crate::leanh::LeanObject,
    mut v___y_4463_: *mut crate::leanh::LeanObject,
    mut v___y_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
    mut v___y_4466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
    return v___x_4468_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___boxed(
    mut v_00_u03b1_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
    mut v___y_4472_: *mut crate::leanh::LeanObject,
    mut v___y_4473_: *mut crate::leanh::LeanObject,
    mut v___y_4474_: *mut crate::leanh::LeanObject,
    mut v___y_4475_: *mut crate::leanh::LeanObject,
    mut v___y_4476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(v_00_u03b1_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
    crate::leanh::lean_dec(v___y_4475_);
    crate::leanh::lean_dec_ref(v___y_4474_);
    crate::leanh::lean_dec(v___y_4473_);
    crate::leanh::lean_dec_ref(v___y_4472_);
    crate::leanh::lean_dec(v___y_4471_);
    crate::leanh::lean_dec_ref(v___y_4470_);
    return v_res_4477_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(
    mut v_opts_4478_: *mut crate::leanh::LeanObject,
    mut v_opt_4479_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4480_ = crate::leanh::lean_ctor_get(v_opt_4479_, 0);
    v_defValue_4481_ = crate::leanh::lean_ctor_get(v_opt_4479_, 1);
    v_map_4482_ = crate::leanh::lean_ctor_get(v_opts_4478_, 0);
    v___x_4483_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4482_,
            v_name_4480_,
        );
    if crate::leanh::lean_obj_tag(v___x_4483_) == 0 {
        let mut v___x_4484_: u8 = 0;
        v___x_4484_ = (crate::leanh::lean_unbox(v_defValue_4481_) as u8);
        return v___x_4484_;
    } else {
        let mut v_val_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4485_ = crate::leanh::lean_ctor_get(v___x_4483_, 0);
        crate::leanh::lean_inc(v_val_4485_);
        crate::leanh::lean_dec_ref_known(v___x_4483_, 1);
        if crate::leanh::lean_obj_tag(v_val_4485_) == 1 {
            let mut v_v_4486_: u8 = 0;
            v_v_4486_ = crate::leanh::lean_ctor_get_uint8(v_val_4485_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4485_, 0);
            return v_v_4486_;
        } else {
            let mut v___x_4487_: u8 = 0;
            crate::leanh::lean_dec(v_val_4485_);
            v___x_4487_ = (crate::leanh::lean_unbox(v_defValue_4481_) as u8);
            return v___x_4487_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3___boxed(
    mut v_opts_4488_: *mut crate::leanh::LeanObject,
    mut v_opt_4489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_opts_4488_, v_opt_4489_);
    crate::leanh::lean_dec_ref(v_opt_4489_);
    crate::leanh::lean_dec_ref(v_opts_4488_);
    v_r_4491_ = crate::leanh::lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4492_ = crate::leanh::lean_box(1);
    v___x_4493_ = l_Lean_MessageData_ofFormat(v___x_4492_);
    return v___x_4493_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4497_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2;
    v___x_4498_ = l_Lean_MessageData_ofFormat(v___x_4497_);
    return v___x_4498_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(
    mut v_x_4499_: *mut crate::leanh::LeanObject,
    mut v_x_4500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v_before_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_unused_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4500_) == 0 {
                    return v_x_4499_;
                } else {
                    v_head_4501_ = crate::leanh::lean_ctor_get(v_x_4500_, 0);
                    v_tail_4502_ = crate::leanh::lean_ctor_get(v_x_4500_, 1);
                    v_isSharedCheck_4524_ = (!crate::leanh::lean_is_exclusive(v_x_4500_)) as u8;
                    if v_isSharedCheck_4524_ == 0 {
                        v___x_4504_ = v_x_4500_;
                        v_isShared_4505_ = v_isSharedCheck_4524_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4502_);
                        crate::leanh::lean_inc(v_head_4501_);
                        crate::leanh::lean_dec(v_x_4500_);
                        v___x_4504_ = crate::leanh::lean_box(0);
                        v_isShared_4505_ = v_isSharedCheck_4524_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4506_ = crate::leanh::lean_ctor_get(v_head_4501_, 0);
                v_isSharedCheck_4522_ = (!crate::leanh::lean_is_exclusive(v_head_4501_)) as u8;
                if v_isSharedCheck_4522_ == 0 {
                    v_unused_4523_ = crate::leanh::lean_ctor_get(v_head_4501_, 1);
                    crate::leanh::lean_dec(v_unused_4523_);
                    v___x_4508_ = v_head_4501_;
                    v_isShared_4509_ = v_isSharedCheck_4522_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_4506_);
                    crate::leanh::lean_dec(v_head_4501_);
                    v___x_4508_ = crate::leanh::lean_box(0);
                    v_isShared_4509_ = v_isSharedCheck_4522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4510_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
                if v_isShared_4509_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4508_, 7);
                    crate::leanh::lean_ctor_set(v___x_4508_, 1, v___x_4510_);
                    crate::leanh::lean_ctor_set(v___x_4508_, 0, v_x_4499_);
                    v___x_4512_ = v___x_4508_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_x_4499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 1, v___x_4510_);
                    v___x_4512_ = v_reuseFailAlloc_4521_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4513_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3);
                if v_isShared_4505_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4504_, 7);
                    crate::leanh::lean_ctor_set(v___x_4504_, 1, v___x_4513_);
                    crate::leanh::lean_ctor_set(v___x_4504_, 0, v___x_4512_);
                    v___x_4515_ = v___x_4504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4520_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4520_, 1, v___x_4513_);
                    v___x_4515_ = v_reuseFailAlloc_4520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4516_ = l_Lean_MessageData_ofSyntax(v_before_4506_);
                v___x_4517_ = l_Lean_indentD(v___x_4516_);
                v___x_4518_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4518_, 0, v___x_4515_);
                crate::leanh::lean_ctor_set(v___x_4518_, 1, v___x_4517_);
                v_x_4499_ = v___x_4518_;
                v_x_4500_ = v_tail_4502_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4528_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1;
    v___x_4529_ = l_Lean_MessageData_ofFormat(v___x_4528_);
    return v___x_4529_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(
    mut v_msgData_4530_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: u8 = 0;
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut v_unused_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4534_ = crate::leanh::lean_ctor_get(v___y_4532_, 2);
                v___x_4535_ = l_Lean_Elab_pp_macroStack;
                v___x_4536_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_options_4534_, v___x_4535_);
                if v___x_4536_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_4531_);
                    v___x_4537_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4537_, 0, v_msgData_4530_);
                    return v___x_4537_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_4531_) == 0 {
                        v___x_4538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4538_, 0, v_msgData_4530_);
                        return v___x_4538_;
                    } else {
                        v_head_4539_ = crate::leanh::lean_ctor_get(v_macroStack_4531_, 0);
                        crate::leanh::lean_inc(v_head_4539_);
                        v_after_4540_ = crate::leanh::lean_ctor_get(v_head_4539_, 1);
                        v_isSharedCheck_4555_ =
                            (!crate::leanh::lean_is_exclusive(v_head_4539_)) as u8;
                        if v_isSharedCheck_4555_ == 0 {
                            v_unused_4556_ = crate::leanh::lean_ctor_get(v_head_4539_, 0);
                            crate::leanh::lean_dec(v_unused_4556_);
                            v___x_4542_ = v_head_4539_;
                            v_isShared_4543_ = v_isSharedCheck_4555_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_4540_);
                            crate::leanh::lean_dec(v_head_4539_);
                            v___x_4542_ = crate::leanh::lean_box(0);
                            v_isShared_4543_ = v_isSharedCheck_4555_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
                if v_isShared_4543_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4542_, 7);
                    crate::leanh::lean_ctor_set(v___x_4542_, 1, v___x_4544_);
                    crate::leanh::lean_ctor_set(v___x_4542_, 0, v_msgData_4530_);
                    v___x_4546_ = v___x_4542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_msgData_4530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 1, v___x_4544_);
                    v___x_4546_ = v_reuseFailAlloc_4554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2);
                v___x_4548_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4548_, 0, v___x_4546_);
                crate::leanh::lean_ctor_set(v___x_4548_, 1, v___x_4547_);
                v___x_4549_ = l_Lean_MessageData_ofSyntax(v_after_4540_);
                v___x_4550_ = l_Lean_indentD(v___x_4549_);
                v_msgData_4551_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_4551_, 0, v___x_4548_);
                crate::leanh::lean_ctor_set(v_msgData_4551_, 1, v___x_4550_);
                v___x_4552_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(v_msgData_4551_, v_macroStack_4531_);
                v___x_4553_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4553_, 0, v___x_4552_);
                return v___x_4553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___boxed(
    mut v_msgData_4557_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_4557_, v_macroStack_4558_, v___y_4559_);
    crate::leanh::lean_dec_ref(v___y_4559_);
    return v_res_4561_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(
    mut v_msg_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4570_ = crate::leanh::lean_ctor_get(v___y_4567_, 5);
                v___x_4571_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_4562_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
                v_a_4572_ = crate::leanh::lean_ctor_get(v___x_4571_, 0);
                crate::leanh::lean_inc(v_a_4572_);
                crate::leanh::lean_dec_ref(v___x_4571_);
                v_macroStack_4573_ = crate::leanh::lean_ctor_get(v___y_4563_, 1);
                v___x_4574_ = l_Lean_Elab_getBetterRef(v_ref_4570_, v_macroStack_4573_);
                crate::leanh::lean_inc(v_macroStack_4573_);
                v___x_4575_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_a_4572_, v_macroStack_4573_, v___y_4567_);
                v_a_4576_ = crate::leanh::lean_ctor_get(v___x_4575_, 0);
                v_isSharedCheck_4584_ = (!crate::leanh::lean_is_exclusive(v___x_4575_)) as u8;
                if v_isSharedCheck_4584_ == 0 {
                    v___x_4578_ = v___x_4575_;
                    v_isShared_4579_ = v_isSharedCheck_4584_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4576_);
                    crate::leanh::lean_dec(v___x_4575_);
                    v___x_4578_ = crate::leanh::lean_box(0);
                    v_isShared_4579_ = v_isSharedCheck_4584_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4580_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4580_, 0, v___x_4574_);
                crate::leanh::lean_ctor_set(v___x_4580_, 1, v_a_4576_);
                if v_isShared_4579_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4578_, 1);
                    crate::leanh::lean_ctor_set(v___x_4578_, 0, v___x_4580_);
                    v___x_4582_ = v___x_4578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4580_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg___boxed(
    mut v_msg_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
    mut v___y_4587_: *mut crate::leanh::LeanObject,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
    mut v___y_4592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4593_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(
            v_msg_4585_,
            v___y_4586_,
            v___y_4587_,
            v___y_4588_,
            v___y_4589_,
            v___y_4590_,
            v___y_4591_,
        );
    crate::leanh::lean_dec(v___y_4591_);
    crate::leanh::lean_dec_ref(v___y_4590_);
    crate::leanh::lean_dec(v___y_4589_);
    crate::leanh::lean_dec_ref(v___y_4588_);
    crate::leanh::lean_dec(v___y_4587_);
    crate::leanh::lean_dec_ref(v___y_4586_);
    return v_res_4593_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(
    mut v_eq_4594_: *mut crate::leanh::LeanObject,
    mut v_r_4595_: *mut crate::leanh::LeanObject,
    mut v_p_4596_: *mut crate::leanh::LeanObject,
    mut v_x_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
    mut v___y_4602_: *mut crate::leanh::LeanObject,
    mut v___y_4603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4611_: u8 = 0;
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_a_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4636_: u8 = 0;
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4640_: u8 = 0;
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4605_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_4594_);
                if crate::leanh::lean_obj_tag(v___x_4605_) == 1 {
                    v_val_4606_ = crate::leanh::lean_ctor_get(v___x_4605_, 0);
                    crate::leanh::lean_inc_n(v_val_4606_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4605_, 1);
                    crate::leanh::lean_inc(v_p_4596_);
                    crate::leanh::lean_inc(v_r_4595_);
                    v___x_4607_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(
                        v_val_4606_,
                        v_r_4595_,
                        v_p_4596_,
                        v___y_4598_,
                        v___y_4599_,
                        v___y_4600_,
                        v___y_4601_,
                        v___y_4602_,
                        v___y_4603_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4607_) == 0 {
                        v_a_4608_ = crate::leanh::lean_ctor_get(v___x_4607_, 0);
                        v_isSharedCheck_4632_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4607_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4610_ = v___x_4607_;
                            v_isShared_4611_ = v_isSharedCheck_4632_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4608_);
                            crate::leanh::lean_dec(v___x_4607_);
                            v___x_4610_ = crate::leanh::lean_box(0);
                            v_isShared_4611_ = v_isSharedCheck_4632_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_4606_);
                        crate::leanh::lean_dec(v_p_4596_);
                        crate::leanh::lean_dec(v_r_4595_);
                        v_a_4633_ = crate::leanh::lean_ctor_get(v___x_4607_, 0);
                        v_isSharedCheck_4640_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4607_)) as u8;
                        if v_isSharedCheck_4640_ == 0 {
                            v___x_4635_ = v___x_4607_;
                            v_isShared_4636_ = v_isSharedCheck_4640_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4633_);
                            crate::leanh::lean_dec(v___x_4607_);
                            v___x_4635_ = crate::leanh::lean_box(0);
                            v_isShared_4636_ = v_isSharedCheck_4640_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4605_);
                    crate::leanh::lean_dec(v_p_4596_);
                    crate::leanh::lean_dec(v_r_4595_);
                    v___x_4641_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
                    return v___x_4641_;
                }
            }
            1 => {
                v___x_4612_ = (crate::leanh::lean_unbox(v_a_4608_) as u8);
                crate::leanh::lean_dec(v_a_4608_);
                if v___x_4612_ == 0 {
                    crate::leanh::lean_del_object(v___x_4610_);
                    v___x_4613_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1,
                    );
                    v___x_4614_ = l_Lean_MessageData_ofSyntax(v_r_4595_);
                    v___x_4615_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4615_, 0, v___x_4613_);
                    crate::leanh::lean_ctor_set(v___x_4615_, 1, v___x_4614_);
                    v___x_4616_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3,
                    );
                    v___x_4617_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4617_, 0, v___x_4615_);
                    crate::leanh::lean_ctor_set(v___x_4617_, 1, v___x_4616_);
                    v___x_4618_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_4606_);
                    crate::leanh::lean_dec(v_val_4606_);
                    v___x_4619_ = l_Lean_stringToMessageData(v___x_4618_);
                    v___x_4620_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4620_, 0, v___x_4617_);
                    crate::leanh::lean_ctor_set(v___x_4620_, 1, v___x_4619_);
                    v___x_4621_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5,
                    );
                    v___x_4622_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4622_, 0, v___x_4620_);
                    crate::leanh::lean_ctor_set(v___x_4622_, 1, v___x_4621_);
                    v___x_4623_ = l_Lean_MessageData_ofSyntax(v_p_4596_);
                    v___x_4624_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4624_, 0, v___x_4622_);
                    crate::leanh::lean_ctor_set(v___x_4624_, 1, v___x_4623_);
                    v___x_4625_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7,
                    );
                    v___x_4626_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4626_, 0, v___x_4624_);
                    crate::leanh::lean_ctor_set(v___x_4626_, 1, v___x_4625_);
                    v___x_4627_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_4626_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
                    return v___x_4627_;
                } else {
                    crate::leanh::lean_dec(v_val_4606_);
                    crate::leanh::lean_dec(v_p_4596_);
                    crate::leanh::lean_dec(v_r_4595_);
                    v___x_4628_ = crate::leanh::lean_box(0);
                    if v_isShared_4611_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4610_, 0, v___x_4628_);
                        v___x_4630_ = v___x_4610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4631_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
                        v___x_4630_ = v_reuseFailAlloc_4631_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4630_;
            }
            3 => {
                if v_isShared_4636_ == 0 {
                    v___x_4638_ = v___x_4635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
                    v___x_4638_ = v_reuseFailAlloc_4639_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed(
    mut v_eq_4642_: *mut crate::leanh::LeanObject,
    mut v_r_4643_: *mut crate::leanh::LeanObject,
    mut v_p_4644_: *mut crate::leanh::LeanObject,
    mut v_x_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(
        v_eq_4642_,
        v_r_4643_,
        v_p_4644_,
        v_x_4645_,
        v___y_4646_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
        v___y_4651_,
    );
    crate::leanh::lean_dec(v___y_4651_);
    crate::leanh::lean_dec_ref(v___y_4650_);
    crate::leanh::lean_dec(v___y_4649_);
    crate::leanh::lean_dec_ref(v___y_4648_);
    crate::leanh::lean_dec(v___y_4647_);
    crate::leanh::lean_dec_ref(v___y_4646_);
    crate::leanh::lean_dec_ref(v_x_4645_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(
    mut v_x_4661_: *mut crate::leanh::LeanObject,
    mut v_a_4662_: *mut crate::leanh::LeanObject,
    mut v_a_4663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    v___x_4665_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
    crate::leanh::lean_inc(v_x_4661_);
    v___x_4666_ = l_Lean_Syntax_isOfKind(v_x_4661_, v___x_4665_);
    if v___x_4666_ == 0 {
        let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4661_);
        v___x_4667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
        return v___x_4667_;
    } else {
        let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_eq_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: u8 = 0;
        v___x_4668_ = crate::leanh::lean_unsigned_to_nat(2);
        v_eq_4669_ = l_Lean_Syntax_getArg(v_x_4661_, v___x_4668_);
        v___x_4670_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
        crate::leanh::lean_inc(v_eq_4669_);
        v___x_4671_ = l_Lean_Syntax_isOfKind(v_eq_4669_, v___x_4670_);
        if v___x_4671_ == 0 {
            let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_eq_4669_);
            crate::leanh::lean_dec(v_x_4661_);
            v___x_4672_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
            return v___x_4672_;
        } else {
            let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4673_ = crate::leanh::lean_unsigned_to_nat(1);
            v_r_4674_ = l_Lean_Syntax_getArg(v_x_4661_, v___x_4673_);
            v___x_4675_ = crate::leanh::lean_unsigned_to_nat(3);
            v_p_4676_ = l_Lean_Syntax_getArg(v_x_4661_, v___x_4675_);
            crate::leanh::lean_dec(v_x_4661_);
            v___f_4677_ = crate::leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed
                    as *mut core::ffi::c_void,
                11,
                3,
            );
            crate::leanh::lean_closure_set(v___f_4677_, 0, v_eq_4669_);
            crate::leanh::lean_closure_set(v___f_4677_, 1, v_r_4674_);
            crate::leanh::lean_closure_set(v___f_4677_, 2, v_p_4676_);
            v___x_4678_ =
                l_Lean_Elab_Command_runTermElabM___redArg(v___f_4677_, v_a_4662_, v_a_4663_);
            return v___x_4678_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(
    mut v_x_4679_: *mut crate::leanh::LeanObject,
    mut v_a_4680_: *mut crate::leanh::LeanObject,
    mut v_a_4681_: *mut crate::leanh::LeanObject,
    mut v_a_4682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4683_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(v_x_4679_, v_a_4680_, v_a_4681_);
    crate::leanh::lean_dec(v_a_4681_);
    crate::leanh::lean_dec_ref(v_a_4680_);
    return v_res_4683_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(
    mut v_00_u03b1_4684_: *mut crate::leanh::LeanObject,
    mut v_msg_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4693_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(
            v_msg_4685_,
            v___y_4686_,
            v___y_4687_,
            v___y_4688_,
            v___y_4689_,
            v___y_4690_,
            v___y_4691_,
        );
    return v___x_4693_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___boxed(
    mut v_00_u03b1_4694_: *mut crate::leanh::LeanObject,
    mut v_msg_4695_: *mut crate::leanh::LeanObject,
    mut v___y_4696_: *mut crate::leanh::LeanObject,
    mut v___y_4697_: *mut crate::leanh::LeanObject,
    mut v___y_4698_: *mut crate::leanh::LeanObject,
    mut v___y_4699_: *mut crate::leanh::LeanObject,
    mut v___y_4700_: *mut crate::leanh::LeanObject,
    mut v___y_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4703_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(
        v_00_u03b1_4694_,
        v_msg_4695_,
        v___y_4696_,
        v___y_4697_,
        v___y_4698_,
        v___y_4699_,
        v___y_4700_,
        v___y_4701_,
    );
    crate::leanh::lean_dec(v___y_4701_);
    crate::leanh::lean_dec_ref(v___y_4700_);
    crate::leanh::lean_dec(v___y_4699_);
    crate::leanh::lean_dec_ref(v___y_4698_);
    crate::leanh::lean_dec(v___y_4697_);
    crate::leanh::lean_dec_ref(v___y_4696_);
    return v_res_4703_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(
    mut v_msgData_4704_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4713_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_4704_, v_macroStack_4705_, v___y_4710_);
    return v___x_4713_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___boxed(
    mut v_msgData_4714_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4715_: *mut crate::leanh::LeanObject,
    mut v___y_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
    mut v___y_4722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4723_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(v_msgData_4714_, v_macroStack_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
    crate::leanh::lean_dec(v___y_4721_);
    crate::leanh::lean_dec_ref(v___y_4720_);
    crate::leanh::lean_dec(v___y_4719_);
    crate::leanh::lean_dec_ref(v___y_4718_);
    crate::leanh::lean_dec(v___y_4717_);
    crate::leanh::lean_dec_ref(v___y_4716_);
    return v_res_4723_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4733_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
    v___x_4734_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1;
    v___x_4735_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_4736_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4732_,
        v___x_4733_,
        v___x_4734_,
        v___x_4735_,
    );
    return v___x_4736_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___boxed(
    mut v_a_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
    return v_res_4738_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4765_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1;
    v___x_4766_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6;
    v___x_4767_ = l_Lean_addBuiltinDeclarationRanges(v___x_4765_, v___x_4766_);
    return v___x_4767_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___boxed(
    mut v_a_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4769_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
    return v_res_4769_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4773_ = crate::leanh::lean_box(0);
    v___x_4774_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1;
    v___x_4775_ = l_Lean_mkConst(v___x_4774_, v___x_4773_);
    return v___x_4775_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(
    mut v_e_4776_: *mut crate::leanh::LeanObject,
    mut v_a_4777_: *mut crate::leanh::LeanObject,
    mut v_a_4778_: *mut crate::leanh::LeanObject,
    mut v_a_4779_: *mut crate::leanh::LeanObject,
    mut v_a_4780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: u8 = 0;
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4782_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once), _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
    v___x_4783_ = 1;
    v___x_4784_ = 0;
    v___x_4785_ = l_Lean_Meta_evalExpr___redArg(
        v___x_4782_,
        v_e_4776_,
        v___x_4783_,
        v___x_4784_,
        v_a_4777_,
        v_a_4778_,
        v_a_4779_,
        v_a_4780_,
    );
    return v___x_4785_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___boxed(
    mut v_e_4786_: *mut crate::leanh::LeanObject,
    mut v_a_4787_: *mut crate::leanh::LeanObject,
    mut v_a_4788_: *mut crate::leanh::LeanObject,
    mut v_a_4789_: *mut crate::leanh::LeanObject,
    mut v_a_4790_: *mut crate::leanh::LeanObject,
    mut v_a_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4792_ =
        l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(
            v_e_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_,
        );
    crate::leanh::lean_dec(v_a_4790_);
    crate::leanh::lean_dec_ref(v_a_4789_);
    crate::leanh::lean_dec(v_a_4788_);
    crate::leanh::lean_dec_ref(v_a_4787_);
    return v_res_4792_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4794_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0;
    v___x_4795_ = l_Lean_stringToMessageData(v___x_4794_);
    return v___x_4795_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4797_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2;
    v___x_4798_ = l_Lean_stringToMessageData(v___x_4797_);
    return v___x_4798_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(
    mut v___x_4799_: *mut crate::leanh::LeanObject,
    mut v___x_4800_: *mut crate::leanh::LeanObject,
    mut v___x_4801_: u8,
    mut v___x_4802_: *mut crate::leanh::LeanObject,
    mut v___y_4803_: *mut crate::leanh::LeanObject,
    mut v___y_4804_: *mut crate::leanh::LeanObject,
    mut v___y_4805_: *mut crate::leanh::LeanObject,
    mut v___y_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u8 = 0;
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4830_: u8 = 0;
    let mut v_unused_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4835_: u8 = 0;
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v___x_4845_: u8 = 0;
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v_a_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4860_: u8 = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4864_: u8 = 0;
    let mut v_a_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut v_a_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4876_: u8 = 0;
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4810_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v___x_4799_,
                    v___x_4800_,
                    v___x_4801_,
                    v___x_4801_,
                    v___x_4802_,
                    v___y_4803_,
                    v___y_4804_,
                    v___y_4805_,
                    v___y_4806_,
                    v___y_4807_,
                    v___y_4808_,
                );
                if crate::leanh::lean_obj_tag(v___x_4810_) == 0 {
                    v_a_4811_ = crate::leanh::lean_ctor_get(v___x_4810_, 0);
                    crate::leanh::lean_inc(v_a_4811_);
                    crate::leanh::lean_dec_ref_known(v___x_4810_, 1);
                    v___x_4812_ = 0;
                    v___x_4813_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                        v___x_4812_,
                        v___y_4803_,
                        v___y_4804_,
                        v___y_4805_,
                        v___y_4806_,
                        v___y_4807_,
                        v___y_4808_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4813_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4813_, 1);
                        v___x_4814_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_4811_, v___y_4806_);
                        v_a_4815_ = crate::leanh::lean_ctor_get(v___x_4814_, 0);
                        crate::leanh::lean_inc_n(v_a_4815_, 2);
                        crate::leanh::lean_dec_ref(v___x_4814_);
                        v___x_4816_ = l_Lean_Meta_getMVars(
                            v_a_4815_,
                            v___y_4805_,
                            v___y_4806_,
                            v___y_4807_,
                            v___y_4808_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4816_) == 0 {
                            v_a_4817_ = crate::leanh::lean_ctor_get(v___x_4816_, 0);
                            crate::leanh::lean_inc(v_a_4817_);
                            crate::leanh::lean_dec_ref_known(v___x_4816_, 1);
                            v___x_4818_ = lean_array_get_size(v_a_4817_);
                            v___x_4819_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4820_ = lean_nat_dec_eq(v___x_4818_, v___x_4819_);
                            if v___x_4820_ == 0 {
                                crate::leanh::lean_dec(v_a_4815_);
                                v___x_4821_ = crate::leanh::lean_box(0);
                                v___x_4822_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                                    v_a_4817_,
                                    v___x_4821_,
                                    v___y_4803_,
                                    v___y_4804_,
                                    v___y_4805_,
                                    v___y_4806_,
                                    v___y_4807_,
                                    v___y_4808_,
                                );
                                crate::leanh::lean_dec(v_a_4817_);
                                if crate::leanh::lean_obj_tag(v___x_4822_) == 0 {
                                    v_isSharedCheck_4830_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4822_)) as u8;
                                    if v_isSharedCheck_4830_ == 0 {
                                        v_unused_4831_ =
                                            crate::leanh::lean_ctor_get(v___x_4822_, 0);
                                        crate::leanh::lean_dec(v_unused_4831_);
                                        v___x_4824_ = v___x_4822_;
                                        v_isShared_4825_ = v_isSharedCheck_4830_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_4822_);
                                        v___x_4824_ = crate::leanh::lean_box(0);
                                        v_isShared_4825_ = v_isSharedCheck_4830_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_4832_ = crate::leanh::lean_ctor_get(v___x_4822_, 0);
                                    v_isSharedCheck_4839_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4822_)) as u8;
                                    if v_isSharedCheck_4839_ == 0 {
                                        v___x_4834_ = v___x_4822_;
                                        v_isShared_4835_ = v_isSharedCheck_4839_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4832_);
                                        crate::leanh::lean_dec(v___x_4822_);
                                        v___x_4834_ = crate::leanh::lean_box(0);
                                        v_isShared_4835_ = v_isSharedCheck_4839_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4817_);
                                crate::leanh::lean_inc(v_a_4815_);
                                v___x_4840_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(v_a_4815_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
                                if crate::leanh::lean_obj_tag(v___x_4840_) == 0 {
                                    v_a_4841_ = crate::leanh::lean_ctor_get(v___x_4840_, 0);
                                    v_isSharedCheck_4856_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4840_)) as u8;
                                    if v_isSharedCheck_4856_ == 0 {
                                        v___x_4843_ = v___x_4840_;
                                        v_isShared_4844_ = v_isSharedCheck_4856_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4841_);
                                        crate::leanh::lean_dec(v___x_4840_);
                                        v___x_4843_ = crate::leanh::lean_box(0);
                                        v_isShared_4844_ = v_isSharedCheck_4856_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4815_);
                                    v_a_4857_ = crate::leanh::lean_ctor_get(v___x_4840_, 0);
                                    v_isSharedCheck_4864_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4840_)) as u8;
                                    if v_isSharedCheck_4864_ == 0 {
                                        v___x_4859_ = v___x_4840_;
                                        v_isShared_4860_ = v_isSharedCheck_4864_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4857_);
                                        crate::leanh::lean_dec(v___x_4840_);
                                        v___x_4859_ = crate::leanh::lean_box(0);
                                        v_isShared_4860_ = v_isSharedCheck_4864_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4815_);
                            v_a_4865_ = crate::leanh::lean_ctor_get(v___x_4816_, 0);
                            v_isSharedCheck_4872_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4816_)) as u8;
                            if v_isSharedCheck_4872_ == 0 {
                                v___x_4867_ = v___x_4816_;
                                v_isShared_4868_ = v_isSharedCheck_4872_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4865_);
                                crate::leanh::lean_dec(v___x_4816_);
                                v___x_4867_ = crate::leanh::lean_box(0);
                                v_isShared_4868_ = v_isSharedCheck_4872_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4811_);
                        return v___x_4813_;
                    }
                } else {
                    v_a_4873_ = crate::leanh::lean_ctor_get(v___x_4810_, 0);
                    v_isSharedCheck_4880_ = (!crate::leanh::lean_is_exclusive(v___x_4810_)) as u8;
                    if v_isSharedCheck_4880_ == 0 {
                        v___x_4875_ = v___x_4810_;
                        v_isShared_4876_ = v_isSharedCheck_4880_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4873_);
                        crate::leanh::lean_dec(v___x_4810_);
                        v___x_4875_ = crate::leanh::lean_box(0);
                        v_isShared_4876_ = v_isSharedCheck_4880_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4826_ = crate::leanh::lean_box(0);
                if v_isShared_4825_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4824_, 0, v___x_4826_);
                    v___x_4828_ = v___x_4824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
                    v___x_4828_ = v_reuseFailAlloc_4829_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4828_;
            }
            3 => {
                if v_isShared_4835_ == 0 {
                    v___x_4837_ = v___x_4834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
                    v___x_4837_ = v_reuseFailAlloc_4838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4837_;
            }
            5 => {
                v___x_4845_ = (crate::leanh::lean_unbox(v_a_4841_) as u8);
                crate::leanh::lean_dec(v_a_4841_);
                if v___x_4845_ == 0 {
                    crate::leanh::lean_del_object(v___x_4843_);
                    v___x_4846_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1,
                    );
                    v___x_4847_ = l_Lean_indentExpr(v_a_4815_);
                    v___x_4848_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4848_, 0, v___x_4846_);
                    crate::leanh::lean_ctor_set(v___x_4848_, 1, v___x_4847_);
                    v___x_4849_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3,
                    );
                    v___x_4850_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4850_, 0, v___x_4848_);
                    crate::leanh::lean_ctor_set(v___x_4850_, 1, v___x_4849_);
                    v___x_4851_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_4850_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
                    return v___x_4851_;
                } else {
                    crate::leanh::lean_dec(v_a_4815_);
                    v___x_4852_ = crate::leanh::lean_box(0);
                    if v_isShared_4844_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4843_, 0, v___x_4852_);
                        v___x_4854_ = v___x_4843_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4855_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4852_);
                        v___x_4854_ = v_reuseFailAlloc_4855_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4854_;
            }
            7 => {
                if v_isShared_4860_ == 0 {
                    v___x_4862_ = v___x_4859_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
                    v___x_4862_ = v_reuseFailAlloc_4863_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4862_;
            }
            9 => {
                if v_isShared_4868_ == 0 {
                    v___x_4870_ = v___x_4867_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
                    v___x_4870_ = v_reuseFailAlloc_4871_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4870_;
            }
            11 => {
                if v_isShared_4876_ == 0 {
                    v___x_4878_ = v___x_4875_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
                    v___x_4878_ = v_reuseFailAlloc_4879_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed(
    mut v___x_4881_: *mut crate::leanh::LeanObject,
    mut v___x_4882_: *mut crate::leanh::LeanObject,
    mut v___x_4883_: *mut crate::leanh::LeanObject,
    mut v___x_4884_: *mut crate::leanh::LeanObject,
    mut v___y_4885_: *mut crate::leanh::LeanObject,
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1792__boxed_4892_: u8 = 0;
    let mut v_res_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1792__boxed_4892_ = (crate::leanh::lean_unbox(v___x_4883_) as u8);
    v_res_4893_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(
        v___x_4881_,
        v___x_4882_,
        v___x_1792__boxed_4892_,
        v___x_4884_,
        v___y_4885_,
        v___y_4886_,
        v___y_4887_,
        v___y_4888_,
        v___y_4889_,
        v___y_4890_,
    );
    crate::leanh::lean_dec(v___y_4890_);
    crate::leanh::lean_dec_ref(v___y_4889_);
    crate::leanh::lean_dec(v___y_4888_);
    crate::leanh::lean_dec_ref(v___y_4887_);
    crate::leanh::lean_dec(v___y_4886_);
    crate::leanh::lean_dec_ref(v___y_4885_);
    return v_res_4893_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once), _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
    v___x_4901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4901_, 0, v___x_4900_);
    return v___x_4901_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(
    mut v_x_4902_: *mut crate::leanh::LeanObject,
    mut v_a_4903_: *mut crate::leanh::LeanObject,
    mut v_a_4904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: u8 = 0;
    v___x_4906_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
    crate::leanh::lean_inc(v_x_4902_);
    v___x_4907_ = l_Lean_Syntax_isOfKind(v_x_4902_, v___x_4906_);
    if v___x_4907_ == 0 {
        let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_4902_);
        v___x_4908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
        return v___x_4908_;
    } else {
        let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4909_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4910_ = l_Lean_Syntax_getArg(v_x_4902_, v___x_4909_);
        crate::leanh::lean_dec(v_x_4902_);
        v___x_4911_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once),
            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2,
        );
        v___x_4912_ = crate::leanh::lean_box(0);
        v___x_4913_ = crate::leanh::lean_box((v___x_4907_) as usize);
        v___f_4914_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed as *mut core::ffi::c_void,
            11,
            4,
        );
        crate::leanh::lean_closure_set(v___f_4914_, 0, v___x_4910_);
        crate::leanh::lean_closure_set(v___f_4914_, 1, v___x_4911_);
        crate::leanh::lean_closure_set(v___f_4914_, 2, v___x_4913_);
        crate::leanh::lean_closure_set(v___f_4914_, 3, v___x_4912_);
        v___x_4915_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_4914_, v_a_4903_, v_a_4904_);
        return v___x_4915_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(
    mut v_x_4916_: *mut crate::leanh::LeanObject,
    mut v_a_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4920_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(v_x_4916_, v_a_4917_, v_a_4918_);
    crate::leanh::lean_dec(v_a_4918_);
    crate::leanh::lean_dec_ref(v_a_4917_);
    return v_res_4920_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4929_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4930_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
    v___x_4931_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1;
    v___x_4932_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_4933_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4929_,
        v___x_4930_,
        v___x_4931_,
        v___x_4932_,
    );
    return v___x_4933_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___boxed(
    mut v_a_4934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4935_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
    return v_res_4935_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4962_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1;
    v___x_4963_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6;
    v___x_4964_ = l_Lean_addBuiltinDeclarationRanges(v___x_4962_, v___x_4963_);
    return v___x_4964_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___boxed(
    mut v_a_4965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4966_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
    return v_res_4966_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Guard(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Guard(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Guard(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Guard(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Guard(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Guard(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Guard(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Guard(builtin);
}
