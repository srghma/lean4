// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.MGoal
// Imports: Std.Do.SPred.DerivedLaws Std.Tactic.Do.ProofMode Lean.Elab.Tactic.Basic
use crate::ffi::{
    lean_array_fget, lean_array_get_borrowed, lean_array_get_size, lean_array_pop, lean_array_push,
    lean_array_to_list, lean_array_uget_borrowed, lean_expr_instantiate1, lean_infer_type,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_usize_dec_eq, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_getMainGoal___redArg,
    runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_betaRev,
    l_Lean_Expr_const___override, l_Lean_Expr_constLevels_x21, l_Lean_Expr_consumeMData,
    l_Lean_Expr_fvar___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppFn_x27,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getRevArg_x21, l_Lean_Expr_hasMVar,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_lam___override, l_Lean_Expr_mdata___override,
    l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::l_Lean_Level_succ___override;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_mkLocalDecl;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofList, l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add,
    l_Lean_indentExpr, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_isExprDefEqGuarded, l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_check;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::SubExpr::{l_Lean_SubExpr_Pos_pushNaryArg, l_Lean_SubExpr_Pos_root};
use crate::r#gen::Std::Do::SPred::DerivedLaws::{
    initialize_Std_Do_SPred_DerivedLaws, runtime_initialize_Std_Do_SPred_DerivedLaws,
};
use crate::r#gen::Std::Tactic::Do::ProofMode::{
    initialize_Std_Tactic_Do_ProofMode, runtime_initialize_Std_Tactic_Do_ProofMode,
};
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value) as *mut leanh::LeanObject,5949480926448383572 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 110, 105, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value) as *mut leanh::LeanObject,540998345785676541 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value) as *mut leanh::LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value:
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
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value:
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value:
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
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value:
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
    m_data: [112, 117, 114, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value)
            as *mut leanh::LeanObject,
        7100147834070349651 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value:
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
    m_data: [101, 109, 112, 116, 121, 72, 121, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value)
            as *mut leanh::LeanObject,
        7792321844762638861 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value:
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
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value)
            as *mut leanh::LeanObject,
        11870096045526947150 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value:
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
    m_data: [97, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value)
            as *mut leanh::LeanObject,
        14620467112940626392 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value:
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
    m_data: [116, 114, 117, 101, 95, 97, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value)
            as *mut leanh::LeanObject,
        2230670361559575988 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value:
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
    m_data: [97, 110, 100, 95, 116, 114, 117, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value)
            as *mut leanh::LeanObject,
        11548698969284563040 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value:
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
    m_data: [98, 105, 101, 110, 116, 97, 105, 108, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value:
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
    m_data: [114, 101, 102, 108, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value)
            as *mut leanh::LeanObject,
        8550510443043304393 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value)
            as *mut leanh::LeanObject,
        14477891125163417350 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value:
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
    m_data: [76, 105, 115, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value)
            as *mut leanh::LeanObject,
        18135193680607614554 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value:
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
    m_data: [99, 111, 110, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value)
            as *mut leanh::LeanObject,
        8614124190858717794 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value:
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [77, 71, 111, 97, 108, 69, 110, 116, 97, 105, 108, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        5139300886809190733 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        1041404937882640577 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value)
            as *mut leanh::LeanObject,
        12835071094194112971 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0_value:
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
        78, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value:
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
    m_data: [101, 110, 116, 97, 105, 108, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value)
            as *mut leanh::LeanObject,
        515334035361346902 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 77, 71, 111, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1_value: leanh::LeanStringObject<95> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 95, m_capacity: 95, m_length: 94, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 77, 71, 111, 97, 108, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 77, 71, 111, 97, 108, 46, 102, 105, 110, 100, 72, 121, 112, 63, 46, 103, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2_value: leanh::LeanStringObject<56> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [77, 71, 111, 97, 108, 46, 102, 105, 110, 100, 72, 121, 112, 63, 58, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 119, 105, 116, 104, 111, 117, 116, 32, 112, 114, 111, 112, 101, 114, 32, 109, 101, 116, 97, 100, 97, 116, 97, 58, 32, 123, 101, 125, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        115, 116, 114, 97, 121, 32, 99, 104, 101, 99, 107, 72, 97, 115, 84, 121, 112, 101, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2_value:
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
    m_data: [32, 58, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4_value:
    leanh::LeanStringObject<96> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 96,
    m_capacity: 96,
    m_length: 95,
    m_data: [
        99, 104, 101, 99, 107, 72, 97, 115, 84, 121, 112, 101, 58, 32, 116, 104, 101, 32, 101, 120,
        112, 114, 101, 115, 115, 105, 111, 110, 39, 115, 32, 105, 110, 102, 101, 114, 114, 101,
        100, 32, 116, 121, 112, 101, 32, 97, 110, 100, 32, 105, 116, 115, 32, 101, 120, 112, 101,
        99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 100, 105, 100, 32, 110, 111, 116, 32, 109,
        97, 116, 99, 104, 46, 10, 10, 32, 32, 32, 32, 32, 32, 101, 120, 112, 114, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        10, 10, 32, 32, 32, 32, 32, 32, 104, 97, 115, 32, 105, 110, 102, 101, 114, 114, 101, 100,
        32, 116, 121, 112, 101, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8_value:
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
        10, 10, 32, 32, 32, 32, 32, 32, 98, 117, 116, 32, 116, 104, 101, 32, 101, 120, 112, 101,
        99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 119, 97, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value:
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
    m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value)
            as *mut leanh::LeanObject,
        13771926289831477797 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value)
            as *mut leanh::LeanObject,
        8738205681931236784 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value)
            as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0_value
) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0_value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [65, 109, 98, 105, 101, 110, 116, 32, 115, 116, 97, 116, 101, 32, 108, 105, 115, 116, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0_value:
    leanh::LeanStringObject<55> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        109, 114, 101, 110, 97, 109, 101, 95, 105, 58, 32, 67, 111, 117, 108, 100, 32, 110, 111,
        116, 32, 102, 105, 110, 100, 32, 105, 110, 97, 99, 99, 101, 115, 115, 105, 98, 108, 101,
        32, 104, 121, 112, 111, 116, 104, 101, 115, 101, 115, 32, 102, 111, 114, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2_value:
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
    m_data: [32, 105, 110, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value:
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
        77, 71, 111, 97, 108, 72, 121, 112, 77, 97, 114, 107, 101, 114, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        5139300886809190733 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
            as *mut leanh::LeanObject,
        1041404937882640577 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value)
            as *mut leanh::LeanObject,
        8141127944165067620 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(
    mut v_x_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_data_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: u8 = 0;
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1996_) == 10 {
                    v_data_1997_ = leanh::lean_ctor_get(v_x_1996_, 0);
                    leanh::lean_inc(v_data_1997_);
                    if leanh::lean_obj_tag(v_data_1997_) == 1 {
                        v_head_1998_ = leanh::lean_ctor_get(v_data_1997_, 0);
                        leanh::lean_inc(v_head_1998_);
                        v_fst_1999_ = leanh::lean_ctor_get(v_head_1998_, 0);
                        leanh::lean_inc(v_fst_1999_);
                        if leanh::lean_obj_tag(v_fst_1999_) == 1 {
                            v_pre_2000_ = leanh::lean_ctor_get(v_fst_1999_, 0);
                            if leanh::lean_obj_tag(v_pre_2000_) == 0 {
                                v_expr_2001_ = leanh::lean_ctor_get(v_x_1996_, 1);
                                leanh::lean_inc_ref(v_expr_2001_);
                                leanh::lean_dec_ref_known(v_x_1996_, 2);
                                v_tail_2002_ = leanh::lean_ctor_get(v_data_1997_, 1);
                                leanh::lean_inc(v_tail_2002_);
                                leanh::lean_dec_ref_known(v_data_1997_, 2);
                                v_snd_2003_ = leanh::lean_ctor_get(v_head_1998_, 1);
                                leanh::lean_inc(v_snd_2003_);
                                leanh::lean_dec(v_head_1998_);
                                v_str_2004_ = leanh::lean_ctor_get(v_fst_1999_, 1);
                                leanh::lean_inc_ref(v_str_2004_);
                                leanh::lean_dec_ref_known(v_fst_1999_, 2);
                                v___x_2005_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0;
                                v___x_2006_ = lean_string_dec_eq(v_str_2004_, v___x_2005_);
                                leanh::lean_dec_ref(v_str_2004_);
                                if v___x_2006_ == 0 {
                                    leanh::lean_dec(v_snd_2003_);
                                    leanh::lean_dec(v_tail_2002_);
                                    leanh::lean_dec_ref(v_expr_2001_);
                                    v___x_2007_ = leanh::lean_box(0);
                                    return v___x_2007_;
                                } else {
                                    if leanh::lean_obj_tag(v_snd_2003_) == 2 {
                                        if leanh::lean_obj_tag(v_tail_2002_) == 1 {
                                            v_head_2008_ =
                                                leanh::lean_ctor_get(v_tail_2002_, 0);
                                            leanh::lean_inc(v_head_2008_);
                                            v_fst_2009_ =
                                                leanh::lean_ctor_get(v_head_2008_, 0);
                                            leanh::lean_inc(v_fst_2009_);
                                            if leanh::lean_obj_tag(v_fst_2009_) == 1 {
                                                v_pre_2010_ =
                                                    leanh::lean_ctor_get(v_fst_2009_, 0);
                                                if leanh::lean_obj_tag(v_pre_2010_) == 0 {
                                                    v_v_2011_ =
                                                        leanh::lean_ctor_get(v_snd_2003_, 0);
                                                    leanh::lean_inc(v_v_2011_);
                                                    leanh::lean_dec_ref_known(
                                                        v_snd_2003_,
                                                        1,
                                                    );
                                                    v_tail_2012_ = leanh::lean_ctor_get(
                                                        v_tail_2002_,
                                                        1,
                                                    );
                                                    leanh::lean_inc(v_tail_2012_);
                                                    leanh::lean_dec_ref_known(
                                                        v_tail_2002_,
                                                        2,
                                                    );
                                                    v_snd_2013_ = leanh::lean_ctor_get(
                                                        v_head_2008_,
                                                        1,
                                                    );
                                                    leanh::lean_inc(v_snd_2013_);
                                                    leanh::lean_dec(v_head_2008_);
                                                    v_str_2014_ =
                                                        leanh::lean_ctor_get(v_fst_2009_, 1);
                                                    leanh::lean_inc_ref(v_str_2014_);
                                                    leanh::lean_dec_ref_known(
                                                        v_fst_2009_,
                                                        2,
                                                    );
                                                    v___x_2015_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0;
                                                    v___x_2016_ = lean_string_dec_eq(
                                                        v_str_2014_,
                                                        v___x_2015_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_2014_);
                                                    if v___x_2016_ == 0 {
                                                        leanh::lean_dec(v_snd_2013_);
                                                        leanh::lean_dec(v_tail_2012_);
                                                        leanh::lean_dec(v_v_2011_);
                                                        leanh::lean_dec_ref(v_expr_2001_);
                                                        v___x_2017_ = leanh::lean_box(0);
                                                        return v___x_2017_;
                                                    } else {
                                                        if leanh::lean_obj_tag(v_snd_2013_)
                                                            == 2
                                                        {
                                                            if leanh::lean_obj_tag(
                                                                v_tail_2012_,
                                                            ) == 0
                                                            {
                                                                v_v_2018_ =
                                                                    leanh::lean_ctor_get(
                                                                        v_snd_2013_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2026_ = (!leanh::lean_is_exclusive(v_snd_2013_)) as u8;
                                                                if v_isSharedCheck_2026_ == 0 {
                                                                    v___x_2020_ = v_snd_2013_;
                                                                    v_isShared_2021_ =
                                                                        v_isSharedCheck_2026_;
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_v_2018_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v_snd_2013_,
                                                                    );
                                                                    v___x_2020_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_2021_ =
                                                                        v_isSharedCheck_2026_;
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref_known(
                                                                    v_snd_2013_,
                                                                    1,
                                                                );
                                                                leanh::lean_dec(
                                                                    v_tail_2012_,
                                                                );
                                                                leanh::lean_dec(v_v_2011_);
                                                                leanh::lean_dec_ref(
                                                                    v_expr_2001_,
                                                                );
                                                                v___x_2027_ =
                                                                    leanh::lean_box(0);
                                                                return v___x_2027_;
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_snd_2013_);
                                                            leanh::lean_dec(v_tail_2012_);
                                                            leanh::lean_dec(v_v_2011_);
                                                            leanh::lean_dec_ref(
                                                                v_expr_2001_,
                                                            );
                                                            v___x_2028_ = leanh::lean_box(0);
                                                            return v___x_2028_;
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref_known(
                                                        v_fst_2009_,
                                                        2,
                                                    );
                                                    leanh::lean_dec(v_head_2008_);
                                                    leanh::lean_dec_ref_known(
                                                        v_tail_2002_,
                                                        2,
                                                    );
                                                    leanh::lean_dec_ref_known(
                                                        v_snd_2003_,
                                                        1,
                                                    );
                                                    leanh::lean_dec_ref(v_expr_2001_);
                                                    v___x_2029_ = leanh::lean_box(0);
                                                    return v___x_2029_;
                                                }
                                            } else {
                                                leanh::lean_dec(v_fst_2009_);
                                                leanh::lean_dec(v_head_2008_);
                                                leanh::lean_dec_ref_known(v_tail_2002_, 2);
                                                leanh::lean_dec_ref_known(v_snd_2003_, 1);
                                                leanh::lean_dec_ref(v_expr_2001_);
                                                v___x_2030_ = leanh::lean_box(0);
                                                return v___x_2030_;
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_snd_2003_, 1);
                                            leanh::lean_dec(v_tail_2002_);
                                            leanh::lean_dec_ref(v_expr_2001_);
                                            v___x_2031_ = leanh::lean_box(0);
                                            return v___x_2031_;
                                        }
                                    } else {
                                        leanh::lean_dec(v_snd_2003_);
                                        leanh::lean_dec(v_tail_2002_);
                                        leanh::lean_dec_ref(v_expr_2001_);
                                        v___x_2032_ = leanh::lean_box(0);
                                        return v___x_2032_;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_fst_1999_, 2);
                                leanh::lean_dec_ref_known(v_data_1997_, 2);
                                leanh::lean_dec(v_head_1998_);
                                leanh::lean_dec_ref_known(v_x_1996_, 2);
                                v___x_2033_ = leanh::lean_box(0);
                                return v___x_2033_;
                            }
                        } else {
                            leanh::lean_dec(v_fst_1999_);
                            leanh::lean_dec_ref_known(v_data_1997_, 2);
                            leanh::lean_dec(v_head_1998_);
                            leanh::lean_dec_ref_known(v_x_1996_, 2);
                            v___x_2034_ = leanh::lean_box(0);
                            return v___x_2034_;
                        }
                    } else {
                        leanh::lean_dec(v_data_1997_);
                        leanh::lean_dec_ref_known(v_x_1996_, 2);
                        v___x_2035_ = leanh::lean_box(0);
                        return v___x_2035_;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1996_);
                    v___x_2036_ = leanh::lean_box(0);
                    return v___x_2036_;
                }
            }
            1 => {
                v___x_2022_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2022_, 0, v_v_2011_);
                leanh::lean_ctor_set(v___x_2022_, 1, v_v_2018_);
                leanh::lean_ctor_set(v___x_2022_, 2, v_expr_2001_);
                if v_isShared_2021_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2020_, 1);
                    leanh::lean_ctor_set(v___x_2020_, 0, v___x_2022_);
                    v___x_2024_ = v___x_2020_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2025_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
                    v___x_2024_ = v_reuseFailAlloc_2025_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(
    mut v_hyp_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uniq_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2038_ = leanh::lean_ctor_get(v_hyp_2037_, 0);
    leanh::lean_inc(v_name_2038_);
    v_uniq_2039_ = leanh::lean_ctor_get(v_hyp_2037_, 1);
    leanh::lean_inc(v_uniq_2039_);
    v_p_2040_ = leanh::lean_ctor_get(v_hyp_2037_, 2);
    leanh::lean_inc_ref(v_p_2040_);
    leanh::lean_dec_ref(v_hyp_2037_);
    v___x_2041_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation;
    v___x_2042_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2042_, 0, v_name_2038_);
    v___x_2043_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2043_, 0, v___x_2041_);
    leanh::lean_ctor_set(v___x_2043_, 1, v___x_2042_);
    v___x_2044_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation;
    v___x_2045_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2045_, 0, v_uniq_2039_);
    v___x_2046_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2046_, 0, v___x_2044_);
    leanh::lean_ctor_set(v___x_2046_, 1, v___x_2045_);
    v___x_2047_ = leanh::lean_box(0);
    v___x_2048_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2048_, 0, v___x_2046_);
    leanh::lean_ctor_set(v___x_2048_, 1, v___x_2047_);
    v___x_2049_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2049_, 0, v___x_2043_);
    leanh::lean_ctor_set(v___x_2049_, 1, v___x_2048_);
    v___x_2050_ = l_Lean_Expr_mdata___override(v___x_2049_, v_p_2040_);
    return v___x_2050_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType(
    mut v_u_2058_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2060_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3;
    v___x_2061_ = leanh::lean_box(0);
    v___x_2062_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2062_, 0, v_u_2058_);
    leanh::lean_ctor_set(v___x_2062_, 1, v___x_2061_);
    v___x_2063_ = l_Lean_mkConst(v___x_2060_, v___x_2062_);
    v___x_2064_ = l_Lean_Expr_app___override(v___x_2063_, v_00_u03c3s_2059_);
    return v___x_2064_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(
    mut v_u_2071_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2072_: *mut leanh::LeanObject,
    mut v_p_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1;
    v___x_2075_ = leanh::lean_box(0);
    v___x_2076_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2076_, 0, v_u_2071_);
    leanh::lean_ctor_set(v___x_2076_, 1, v___x_2075_);
    v___x_2077_ = l_Lean_mkConst(v___x_2074_, v___x_2076_);
    v___x_2078_ = l_Lean_mkAppB(v___x_2077_, v_00_u03c3s_2072_, v_p_2073_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(
    mut v_x_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fn_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: u8 = 0;
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_unused_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2079_) == 5 {
                    v_fn_2080_ = leanh::lean_ctor_get(v_x_2079_, 0);
                    leanh::lean_inc_ref(v_fn_2080_);
                    if leanh::lean_obj_tag(v_fn_2080_) == 5 {
                        v_fn_2081_ = leanh::lean_ctor_get(v_fn_2080_, 0);
                        leanh::lean_inc_ref(v_fn_2081_);
                        if leanh::lean_obj_tag(v_fn_2081_) == 4 {
                            v_declName_2082_ = leanh::lean_ctor_get(v_fn_2081_, 0);
                            leanh::lean_inc(v_declName_2082_);
                            if leanh::lean_obj_tag(v_declName_2082_) == 1 {
                                v_pre_2083_ = leanh::lean_ctor_get(v_declName_2082_, 0);
                                leanh::lean_inc(v_pre_2083_);
                                if leanh::lean_obj_tag(v_pre_2083_) == 1 {
                                    v_pre_2084_ = leanh::lean_ctor_get(v_pre_2083_, 0);
                                    leanh::lean_inc(v_pre_2084_);
                                    if leanh::lean_obj_tag(v_pre_2084_) == 1 {
                                        v_pre_2085_ = leanh::lean_ctor_get(v_pre_2084_, 0);
                                        leanh::lean_inc(v_pre_2085_);
                                        if leanh::lean_obj_tag(v_pre_2085_) == 1 {
                                            v_pre_2086_ =
                                                leanh::lean_ctor_get(v_pre_2085_, 0);
                                            if leanh::lean_obj_tag(v_pre_2086_) == 0 {
                                                v_arg_2087_ =
                                                    leanh::lean_ctor_get(v_x_2079_, 1);
                                                leanh::lean_inc_ref(v_arg_2087_);
                                                leanh::lean_dec_ref_known(v_x_2079_, 2);
                                                v_arg_2088_ =
                                                    leanh::lean_ctor_get(v_fn_2080_, 1);
                                                leanh::lean_inc_ref(v_arg_2088_);
                                                leanh::lean_dec_ref_known(v_fn_2080_, 2);
                                                v_us_2089_ =
                                                    leanh::lean_ctor_get(v_fn_2081_, 1);
                                                leanh::lean_inc(v_us_2089_);
                                                leanh::lean_dec_ref_known(v_fn_2081_, 2);
                                                v_str_2090_ = leanh::lean_ctor_get(
                                                    v_declName_2082_,
                                                    1,
                                                );
                                                leanh::lean_inc_ref(v_str_2090_);
                                                leanh::lean_dec_ref_known(
                                                    v_declName_2082_,
                                                    2,
                                                );
                                                v_str_2091_ =
                                                    leanh::lean_ctor_get(v_pre_2083_, 1);
                                                leanh::lean_inc_ref(v_str_2091_);
                                                leanh::lean_dec_ref_known(v_pre_2083_, 2);
                                                v_str_2092_ =
                                                    leanh::lean_ctor_get(v_pre_2084_, 1);
                                                leanh::lean_inc_ref(v_str_2092_);
                                                leanh::lean_dec_ref_known(v_pre_2084_, 2);
                                                v_str_2093_ =
                                                    leanh::lean_ctor_get(v_pre_2085_, 1);
                                                leanh::lean_inc_ref(v_str_2093_);
                                                leanh::lean_dec_ref_known(v_pre_2085_, 2);
                                                v___x_2094_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0;
                                                v___x_2095_ =
                                                    lean_string_dec_eq(v_str_2093_, v___x_2094_);
                                                leanh::lean_dec_ref(v_str_2093_);
                                                if v___x_2095_ == 0 {
                                                    leanh::lean_dec_ref(v_str_2092_);
                                                    leanh::lean_dec_ref(v_str_2091_);
                                                    leanh::lean_dec_ref(v_str_2090_);
                                                    leanh::lean_dec(v_us_2089_);
                                                    leanh::lean_dec_ref(v_arg_2088_);
                                                    leanh::lean_dec_ref(v_arg_2087_);
                                                    v___x_2096_ = leanh::lean_box(0);
                                                    return v___x_2096_;
                                                } else {
                                                    v___x_2097_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1;
                                                    v___x_2098_ = lean_string_dec_eq(
                                                        v_str_2092_,
                                                        v___x_2097_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_2092_);
                                                    if v___x_2098_ == 0 {
                                                        leanh::lean_dec_ref(v_str_2091_);
                                                        leanh::lean_dec_ref(v_str_2090_);
                                                        leanh::lean_dec(v_us_2089_);
                                                        leanh::lean_dec_ref(v_arg_2088_);
                                                        leanh::lean_dec_ref(v_arg_2087_);
                                                        v___x_2099_ = leanh::lean_box(0);
                                                        return v___x_2099_;
                                                    } else {
                                                        v___x_2100_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2;
                                                        v___x_2101_ = lean_string_dec_eq(
                                                            v_str_2091_,
                                                            v___x_2100_,
                                                        );
                                                        leanh::lean_dec_ref(v_str_2091_);
                                                        if v___x_2101_ == 0 {
                                                            leanh::lean_dec_ref(v_str_2090_);
                                                            leanh::lean_dec(v_us_2089_);
                                                            leanh::lean_dec_ref(v_arg_2088_);
                                                            leanh::lean_dec_ref(v_arg_2087_);
                                                            v___x_2102_ = leanh::lean_box(0);
                                                            return v___x_2102_;
                                                        } else {
                                                            v___x_2103_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0;
                                                            v___x_2104_ = lean_string_dec_eq(
                                                                v_str_2090_,
                                                                v___x_2103_,
                                                            );
                                                            leanh::lean_dec_ref(v_str_2090_);
                                                            if v___x_2104_ == 0 {
                                                                leanh::lean_dec(v_us_2089_);
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2088_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_2087_,
                                                                );
                                                                v___x_2105_ =
                                                                    leanh::lean_box(0);
                                                                return v___x_2105_;
                                                            } else {
                                                                if leanh::lean_obj_tag(
                                                                    v_us_2089_,
                                                                ) == 1
                                                                {
                                                                    v_tail_2106_ =
                                                                        leanh::lean_ctor_get(
                                                                            v_us_2089_, 1,
                                                                        );
                                                                    if leanh::lean_obj_tag(
                                                                        v_tail_2106_,
                                                                    ) == 0
                                                                    {
                                                                        v_head_2107_ = leanh::lean_ctor_get(v_us_2089_, 0);
                                                                        v_isSharedCheck_2116_ = (!leanh::lean_is_exclusive(v_us_2089_)) as u8;
                                                                        if v_isSharedCheck_2116_
                                                                            == 0
                                                                        {
                                                                            v_unused_2117_ = leanh::lean_ctor_get(v_us_2089_, 1);
                                                                            leanh::lean_dec(
                                                                                v_unused_2117_,
                                                                            );
                                                                            v___x_2109_ =
                                                                                v_us_2089_;
                                                                            v_isShared_2110_ = v_isSharedCheck_2116_;
                                                                            state = 1;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_head_2107_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v_us_2089_,
                                                                            );
                                                                            v___x_2109_ = leanh::lean_box(0);
                                                                            v_isShared_2110_ = v_isSharedCheck_2116_;
                                                                            state = 1;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref_known(v_us_2089_, 2);
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_2088_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_2087_,
                                                                        );
                                                                        v___x_2118_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        return v___x_2118_;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_us_2089_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_2088_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_2087_,
                                                                    );
                                                                    v___x_2119_ =
                                                                        leanh::lean_box(0);
                                                                    return v___x_2119_;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref_known(v_pre_2085_, 2);
                                                leanh::lean_dec_ref_known(v_pre_2084_, 2);
                                                leanh::lean_dec_ref_known(v_pre_2083_, 2);
                                                leanh::lean_dec_ref_known(
                                                    v_declName_2082_,
                                                    2,
                                                );
                                                leanh::lean_dec_ref_known(v_fn_2081_, 2);
                                                leanh::lean_dec_ref_known(v_fn_2080_, 2);
                                                leanh::lean_dec_ref_known(v_x_2079_, 2);
                                                v___x_2120_ = leanh::lean_box(0);
                                                return v___x_2120_;
                                            }
                                        } else {
                                            leanh::lean_dec(v_pre_2085_);
                                            leanh::lean_dec_ref_known(v_pre_2084_, 2);
                                            leanh::lean_dec_ref_known(v_pre_2083_, 2);
                                            leanh::lean_dec_ref_known(v_declName_2082_, 2);
                                            leanh::lean_dec_ref_known(v_fn_2081_, 2);
                                            leanh::lean_dec_ref_known(v_fn_2080_, 2);
                                            leanh::lean_dec_ref_known(v_x_2079_, 2);
                                            v___x_2121_ = leanh::lean_box(0);
                                            return v___x_2121_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_pre_2083_, 2);
                                        leanh::lean_dec(v_pre_2084_);
                                        leanh::lean_dec_ref_known(v_declName_2082_, 2);
                                        leanh::lean_dec_ref_known(v_fn_2081_, 2);
                                        leanh::lean_dec_ref_known(v_fn_2080_, 2);
                                        leanh::lean_dec_ref_known(v_x_2079_, 2);
                                        v___x_2122_ = leanh::lean_box(0);
                                        return v___x_2122_;
                                    }
                                } else {
                                    leanh::lean_dec(v_pre_2083_);
                                    leanh::lean_dec_ref_known(v_declName_2082_, 2);
                                    leanh::lean_dec_ref_known(v_fn_2081_, 2);
                                    leanh::lean_dec_ref_known(v_fn_2080_, 2);
                                    leanh::lean_dec_ref_known(v_x_2079_, 2);
                                    v___x_2123_ = leanh::lean_box(0);
                                    return v___x_2123_;
                                }
                            } else {
                                leanh::lean_dec(v_declName_2082_);
                                leanh::lean_dec_ref_known(v_fn_2081_, 2);
                                leanh::lean_dec_ref_known(v_fn_2080_, 2);
                                leanh::lean_dec_ref_known(v_x_2079_, 2);
                                v___x_2124_ = leanh::lean_box(0);
                                return v___x_2124_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_fn_2081_);
                            leanh::lean_dec_ref_known(v_fn_2080_, 2);
                            leanh::lean_dec_ref_known(v_x_2079_, 2);
                            v___x_2125_ = leanh::lean_box(0);
                            return v___x_2125_;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_x_2079_, 2);
                        leanh::lean_dec_ref(v_fn_2080_);
                        v___x_2126_ = leanh::lean_box(0);
                        return v___x_2126_;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2079_);
                    v___x_2127_ = leanh::lean_box(0);
                    return v___x_2127_;
                }
            }
            1 => {
                if v_isShared_2110_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2109_, 0);
                    leanh::lean_ctor_set(v___x_2109_, 1, v_arg_2087_);
                    leanh::lean_ctor_set(v___x_2109_, 0, v_arg_2088_);
                    v___x_2112_ = v___x_2109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_arg_2088_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_arg_2087_);
                    v___x_2112_ = v_reuseFailAlloc_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2113_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2113_, 0, v_head_2107_);
                leanh::lean_ctor_set(v___x_2113_, 1, v___x_2112_);
                v___x_2114_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2135_ = leanh::lean_box(0);
    v___x_2136_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1;
    v___x_2137_ = l_Lean_mkConst(v___x_2136_, v___x_2135_);
    return v___x_2137_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(
    mut v_u_2138_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName;
    v___x_2141_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2,
    );
    v___x_2142_ =
        l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_2138_, v_00_u03c3s_2139_, v___x_2141_);
    v___x_2143_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2143_, 0, v___x_2140_);
    leanh::lean_ctor_set(v___x_2143_, 1, v___x_2140_);
    leanh::lean_ctor_set(v___x_2143_, 2, v___x_2142_);
    v___x_2144_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(
    mut v_e_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: u8 = 0;
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v_snd_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v_str_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_unused_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2146_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_2145_);
                if leanh::lean_obj_tag(v___x_2146_) == 0 {
                    v___x_2147_ = leanh::lean_box(0);
                    return v___x_2147_;
                } else {
                    v_val_2148_ = leanh::lean_ctor_get(v___x_2146_, 0);
                    leanh::lean_inc(v_val_2148_);
                    leanh::lean_dec_ref_known(v___x_2146_, 1);
                    v_name_2149_ = leanh::lean_ctor_get(v_val_2148_, 0);
                    leanh::lean_inc(v_name_2149_);
                    v_p_2150_ = leanh::lean_ctor_get(v_val_2148_, 2);
                    leanh::lean_inc_ref(v_p_2150_);
                    leanh::lean_dec(v_val_2148_);
                    v___x_2185_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName;
                    v___x_2186_ = lean_name_eq(v_name_2149_, v___x_2185_);
                    if v___x_2186_ == 0 {
                        v___x_2187_ = l_Lean_Name_hasMacroScopes(v_name_2149_);
                        leanh::lean_dec(v_name_2149_);
                        v___y_2152_ = v___x_2187_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_name_2149_);
                        v___y_2152_ = v___x_2186_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2152_ == 0 {
                    leanh::lean_dec_ref(v_p_2150_);
                    v___x_2153_ = leanh::lean_box(0);
                    return v___x_2153_;
                } else {
                    v___x_2154_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(v_p_2150_);
                    if leanh::lean_obj_tag(v___x_2154_) == 0 {
                        v___x_2155_ = leanh::lean_box(0);
                        return v___x_2155_;
                    } else {
                        v_val_2156_ = leanh::lean_ctor_get(v___x_2154_, 0);
                        v_isSharedCheck_2184_ =
                            (!leanh::lean_is_exclusive(v___x_2154_)) as u8;
                        if v_isSharedCheck_2184_ == 0 {
                            v___x_2158_ = v___x_2154_;
                            v_isShared_2159_ = v_isSharedCheck_2184_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_2156_);
                            leanh::lean_dec(v___x_2154_);
                            v___x_2158_ = leanh::lean_box(0);
                            v_isShared_2159_ = v_isSharedCheck_2184_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_snd_2160_ = leanh::lean_ctor_get(v_val_2156_, 1);
                leanh::lean_inc(v_snd_2160_);
                v_snd_2161_ = leanh::lean_ctor_get(v_snd_2160_, 1);
                if leanh::lean_obj_tag(v_snd_2161_) == 4 {
                    v_declName_2162_ = leanh::lean_ctor_get(v_snd_2161_, 0);
                    leanh::lean_inc(v_declName_2162_);
                    if leanh::lean_obj_tag(v_declName_2162_) == 1 {
                        v_pre_2163_ = leanh::lean_ctor_get(v_declName_2162_, 0);
                        if leanh::lean_obj_tag(v_pre_2163_) == 0 {
                            v_fst_2164_ = leanh::lean_ctor_get(v_val_2156_, 0);
                            leanh::lean_inc(v_fst_2164_);
                            leanh::lean_dec(v_val_2156_);
                            v_fst_2165_ = leanh::lean_ctor_get(v_snd_2160_, 0);
                            v_isSharedCheck_2179_ =
                                (!leanh::lean_is_exclusive(v_snd_2160_)) as u8;
                            if v_isSharedCheck_2179_ == 0 {
                                v_unused_2180_ = leanh::lean_ctor_get(v_snd_2160_, 1);
                                leanh::lean_dec(v_unused_2180_);
                                v___x_2167_ = v_snd_2160_;
                                v_isShared_2168_ = v_isSharedCheck_2179_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_fst_2165_);
                                leanh::lean_dec(v_snd_2160_);
                                v___x_2167_ = leanh::lean_box(0);
                                v_isShared_2168_ = v_isSharedCheck_2179_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_declName_2162_, 2);
                            leanh::lean_dec(v_snd_2160_);
                            leanh::lean_del_object(v___x_2158_);
                            leanh::lean_dec(v_val_2156_);
                            v___x_2181_ = leanh::lean_box(0);
                            return v___x_2181_;
                        }
                    } else {
                        leanh::lean_dec(v_declName_2162_);
                        leanh::lean_dec(v_snd_2160_);
                        leanh::lean_del_object(v___x_2158_);
                        leanh::lean_dec(v_val_2156_);
                        v___x_2182_ = leanh::lean_box(0);
                        return v___x_2182_;
                    }
                } else {
                    leanh::lean_dec(v_snd_2160_);
                    leanh::lean_del_object(v___x_2158_);
                    leanh::lean_dec(v_val_2156_);
                    v___x_2183_ = leanh::lean_box(0);
                    return v___x_2183_;
                }
            }
            3 => {
                v_str_2169_ = leanh::lean_ctor_get(v_declName_2162_, 1);
                leanh::lean_inc_ref(v_str_2169_);
                leanh::lean_dec_ref_known(v_declName_2162_, 2);
                v___x_2170_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0;
                v___x_2171_ = lean_string_dec_eq(v_str_2169_, v___x_2170_);
                leanh::lean_dec_ref(v_str_2169_);
                if v___x_2171_ == 0 {
                    leanh::lean_del_object(v___x_2167_);
                    leanh::lean_dec(v_fst_2165_);
                    leanh::lean_dec(v_fst_2164_);
                    leanh::lean_del_object(v___x_2158_);
                    v___x_2172_ = leanh::lean_box(0);
                    return v___x_2172_;
                } else {
                    if v_isShared_2168_ == 0 {
                        leanh::lean_ctor_set(v___x_2167_, 1, v_fst_2165_);
                        leanh::lean_ctor_set(v___x_2167_, 0, v_fst_2164_);
                        v___x_2174_ = v___x_2167_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2178_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_fst_2164_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_fst_2165_);
                        v___x_2174_ = v_reuseFailAlloc_2178_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2159_ == 0 {
                    leanh::lean_ctor_set(v___x_2158_, 0, v___x_2174_);
                    v___x_2176_ = v___x_2158_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
                    v___x_2176_ = v_reuseFailAlloc_2177_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(
    mut v_pos_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2189_ = leanh::lean_unsigned_to_nat(3);
    v___x_2190_ = leanh::lean_unsigned_to_nat(1);
    v___x_2191_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_2189_, v___x_2190_, v_pos_2188_);
    return v___x_2191_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct___boxed(
    mut v_pos_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_pos_2192_);
    leanh::lean_dec(v_pos_2192_);
    return v_res_2193_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(
    mut v_pos_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = leanh::lean_unsigned_to_nat(3);
    v___x_2196_ = leanh::lean_unsigned_to_nat(2);
    v___x_2197_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_2195_, v___x_2196_, v_pos_2194_);
    return v___x_2197_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct___boxed(
    mut v_pos_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2199_ = l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_pos_2198_);
    leanh::lean_dec(v_pos_2198_);
    return v_res_2199_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
    mut v_u_2206_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2207_: *mut leanh::LeanObject,
    mut v_lhs_2208_: *mut leanh::LeanObject,
    mut v_rhs_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1;
    v___x_2211_ = leanh::lean_box(0);
    v___x_2212_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2212_, 0, v_u_2206_);
    leanh::lean_ctor_set(v___x_2212_, 1, v___x_2211_);
    v___x_2213_ = l_Lean_mkConst(v___x_2210_, v___x_2212_);
    v___x_2214_ = l_Lean_mkApp3(v___x_2213_, v_00_u03c3s_2207_, v_lhs_2208_, v_rhs_2209_);
    return v___x_2214_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
    mut v_u_2235_: *mut leanh::LeanObject,
    mut v_00_u03c3s_2236_: *mut leanh::LeanObject,
    mut v_lhs_2237_: *mut leanh::LeanObject,
    mut v_rhs_2238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_lhs_2237_);
    v___x_2239_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_lhs_2237_);
    if leanh::lean_obj_tag(v___x_2239_) == 1 {
        let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_2239_, 1);
        leanh::lean_dec_ref(v_lhs_2237_);
        v___x_2240_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1;
        v___x_2241_ = leanh::lean_box(0);
        v___x_2242_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2242_, 0, v_u_2235_);
        leanh::lean_ctor_set(v___x_2242_, 1, v___x_2241_);
        v___x_2243_ = l_Lean_mkConst(v___x_2240_, v___x_2242_);
        leanh::lean_inc_ref(v_rhs_2238_);
        v___x_2244_ = l_Lean_mkAppB(v___x_2243_, v_00_u03c3s_2236_, v_rhs_2238_);
        v___x_2245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2245_, 0, v_rhs_2238_);
        leanh::lean_ctor_set(v___x_2245_, 1, v___x_2244_);
        return v___x_2245_;
    } else {
        let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_2239_);
        leanh::lean_inc_ref(v_rhs_2238_);
        v___x_2246_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_rhs_2238_);
        if leanh::lean_obj_tag(v___x_2246_) == 1 {
            let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_2246_, 1);
            leanh::lean_dec_ref(v_rhs_2238_);
            v___x_2247_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3;
            v___x_2248_ = leanh::lean_box(0);
            v___x_2249_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2249_, 0, v_u_2235_);
            leanh::lean_ctor_set(v___x_2249_, 1, v___x_2248_);
            v___x_2250_ = l_Lean_mkConst(v___x_2247_, v___x_2249_);
            leanh::lean_inc_ref(v_lhs_2237_);
            v___x_2251_ = l_Lean_mkAppB(v___x_2250_, v_00_u03c3s_2236_, v_lhs_2237_);
            v___x_2252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2252_, 0, v_lhs_2237_);
            leanh::lean_ctor_set(v___x_2252_, 1, v___x_2251_);
            return v___x_2252_;
        } else {
            let mut v_result_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_2246_);
            leanh::lean_inc_ref(v_00_u03c3s_2236_);
            leanh::lean_inc(v_u_2235_);
            v_result_2253_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                v_u_2235_,
                v_00_u03c3s_2236_,
                v_lhs_2237_,
                v_rhs_2238_,
            );
            v___x_2254_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6;
            v___x_2255_ = leanh::lean_box(0);
            v___x_2256_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2256_, 0, v_u_2235_);
            leanh::lean_ctor_set(v___x_2256_, 1, v___x_2255_);
            v___x_2257_ = l_Lean_mkConst(v___x_2254_, v___x_2256_);
            leanh::lean_inc_ref(v_result_2253_);
            v___x_2258_ = l_Lean_mkAppB(v___x_2257_, v_00_u03c3s_2236_, v_result_2253_);
            v___x_2259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_2259_, 0, v_result_2253_);
            leanh::lean_ctor_set(v___x_2259_, 1, v___x_2258_);
            return v___x_2259_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(
    mut v_u_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1;
    v___x_2265_ = l_Lean_Level_succ___override(v_u_2263_);
    v___x_2266_ = leanh::lean_box(0);
    leanh::lean_inc(v___x_2265_);
    v___x_2267_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2267_, 0, v___x_2265_);
    leanh::lean_ctor_set(v___x_2267_, 1, v___x_2266_);
    v___x_2268_ = l_Lean_mkConst(v___x_2264_, v___x_2267_);
    v___x_2269_ = l_Lean_mkSort(v___x_2265_);
    v___x_2270_ = l_Lean_Expr_app___override(v___x_2268_, v___x_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(
    mut v_u_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1;
    v___x_2277_ = l_Lean_Level_succ___override(v_u_2275_);
    v___x_2278_ = leanh::lean_box(0);
    leanh::lean_inc(v___x_2277_);
    v___x_2279_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2277_);
    leanh::lean_ctor_set(v___x_2279_, 1, v___x_2278_);
    v___x_2280_ = l_Lean_mkConst(v___x_2276_, v___x_2279_);
    v___x_2281_ = l_Lean_mkSort(v___x_2277_);
    v___x_2282_ = l_Lean_Expr_app___override(v___x_2280_, v___x_2281_);
    return v___x_2282_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(
    mut v_u_2287_: *mut leanh::LeanObject,
    mut v_hd_2288_: *mut leanh::LeanObject,
    mut v_tl_2289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2290_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1;
    v___x_2291_ = l_Lean_Level_succ___override(v_u_2287_);
    v___x_2292_ = leanh::lean_box(0);
    leanh::lean_inc(v___x_2291_);
    v___x_2293_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2293_, 0, v___x_2291_);
    leanh::lean_ctor_set(v___x_2293_, 1, v___x_2292_);
    v___x_2294_ = l_Lean_mkConst(v___x_2290_, v___x_2293_);
    v___x_2295_ = l_Lean_mkSort(v___x_2291_);
    v___x_2296_ = l_Lean_mkApp3(v___x_2294_, v___x_2295_, v_hd_2288_, v_tl_2289_);
    return v___x_2296_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(
    mut v_a_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut v_isSharedCheck_2336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2303_ = leanh::lean_ctor_get(v_a_2297_, 0);
                v_snd_2304_ = leanh::lean_ctor_get(v_a_2297_, 1);
                v_isSharedCheck_2336_ = (!leanh::lean_is_exclusive(v_a_2297_)) as u8;
                if v_isSharedCheck_2336_ == 0 {
                    v___x_2306_ = v_a_2297_;
                    v_isShared_2307_ = v_isSharedCheck_2336_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2304_);
                    leanh::lean_inc(v_fst_2303_);
                    leanh::lean_dec(v_a_2297_);
                    v___x_2306_ = leanh::lean_box(0);
                    v_isShared_2307_ = v_isSharedCheck_2336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2308_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1;
                v___x_2309_ = leanh::lean_unsigned_to_nat(3);
                v___x_2310_ = l_Lean_Expr_isAppOfArity(v_fst_2303_, v___x_2308_, v___x_2309_);
                if v___x_2310_ == 0 {
                    if v_isShared_2307_ == 0 {
                        v___x_2312_ = v___x_2306_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2314_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_fst_2303_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_snd_2304_);
                        v___x_2312_ = v_reuseFailAlloc_2314_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2315_ = leanh::lean_unsigned_to_nat(2);
                    v___x_2316_ = l_Lean_Expr_getAppNumArgs(v_fst_2303_);
                    v___x_2317_ = lean_nat_sub(v___x_2316_, v___x_2315_);
                    leanh::lean_dec(v___x_2316_);
                    v___x_2318_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2319_ = lean_nat_sub(v___x_2317_, v___x_2318_);
                    leanh::lean_dec(v___x_2317_);
                    v___x_2320_ = l_Lean_Expr_getRevArg_x21(v_fst_2303_, v___x_2319_);
                    leanh::lean_dec(v_fst_2303_);
                    v___x_2321_ = l_Lean_Meta_whnfR(
                        v___x_2320_,
                        v___y_2298_,
                        v___y_2299_,
                        v___y_2300_,
                        v___y_2301_,
                    );
                    if leanh::lean_obj_tag(v___x_2321_) == 0 {
                        v_a_2322_ = leanh::lean_ctor_get(v___x_2321_, 0);
                        leanh::lean_inc(v_a_2322_);
                        leanh::lean_dec_ref_known(v___x_2321_, 1);
                        v___x_2323_ = lean_nat_add(v_snd_2304_, v___x_2318_);
                        leanh::lean_dec(v_snd_2304_);
                        if v_isShared_2307_ == 0 {
                            leanh::lean_ctor_set(v___x_2306_, 1, v___x_2323_);
                            leanh::lean_ctor_set(v___x_2306_, 0, v_a_2322_);
                            v___x_2325_ = v___x_2306_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2327_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2322_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2323_);
                            v___x_2325_ = v_reuseFailAlloc_2327_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2306_);
                        leanh::lean_dec(v_snd_2304_);
                        v_a_2328_ = leanh::lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2335_ =
                            (!leanh::lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2335_ == 0 {
                            v___x_2330_ = v___x_2321_;
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2328_);
                            leanh::lean_dec(v___x_2321_);
                            v___x_2330_ = leanh::lean_box(0);
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_2313_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2313_, 0, v___x_2312_);
                return v___x_2313_;
            }
            3 => {
                v_a_2297_ = v___x_2325_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2331_ == 0 {
                    v___x_2333_ = v___x_2330_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2334_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
                    v___x_2333_ = v_reuseFailAlloc_2334_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg___boxed(
    mut v_a_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
    mut v___y_2339_: *mut leanh::LeanObject,
    mut v___y_2340_: *mut leanh::LeanObject,
    mut v___y_2341_: *mut leanh::LeanObject,
    mut v___y_2342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2343_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    leanh::lean_dec(v___y_2341_);
    leanh::lean_dec_ref(v___y_2340_);
    leanh::lean_dec(v___y_2339_);
    leanh::lean_dec_ref(v___y_2338_);
    return v_res_2343_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(
    mut v_00_u03c3s_2344_: *mut leanh::LeanObject,
    mut v_a_2345_: *mut leanh::LeanObject,
    mut v_a_2346_: *mut leanh::LeanObject,
    mut v_a_2347_: *mut leanh::LeanObject,
    mut v_a_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v_snd_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_a_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_a_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2350_ = l_Lean_Meta_whnfR(
                    v_00_u03c3s_2344_,
                    v_a_2345_,
                    v_a_2346_,
                    v_a_2347_,
                    v_a_2348_,
                );
                if leanh::lean_obj_tag(v___x_2350_) == 0 {
                    v_a_2351_ = leanh::lean_ctor_get(v___x_2350_, 0);
                    leanh::lean_inc(v_a_2351_);
                    leanh::lean_dec_ref_known(v___x_2350_, 1);
                    v___x_2352_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2353_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2353_, 0, v_a_2351_);
                    leanh::lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                    v___x_2354_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v___x_2353_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
                    if leanh::lean_obj_tag(v___x_2354_) == 0 {
                        v_a_2355_ = leanh::lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2363_ =
                            (!leanh::lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2363_ == 0 {
                            v___x_2357_ = v___x_2354_;
                            v_isShared_2358_ = v_isSharedCheck_2363_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2355_);
                            leanh::lean_dec(v___x_2354_);
                            v___x_2357_ = leanh::lean_box(0);
                            v_isShared_2358_ = v_isSharedCheck_2363_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2364_ = leanh::lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2371_ =
                            (!leanh::lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2371_ == 0 {
                            v___x_2366_ = v___x_2354_;
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2364_);
                            leanh::lean_dec(v___x_2354_);
                            v___x_2366_ = leanh::lean_box(0);
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2372_ = leanh::lean_ctor_get(v___x_2350_, 0);
                    v_isSharedCheck_2379_ = (!leanh::lean_is_exclusive(v___x_2350_)) as u8;
                    if v_isSharedCheck_2379_ == 0 {
                        v___x_2374_ = v___x_2350_;
                        v_isShared_2375_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2372_);
                        leanh::lean_dec(v___x_2350_);
                        v___x_2374_ = leanh::lean_box(0);
                        v_isShared_2375_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2359_ = leanh::lean_ctor_get(v_a_2355_, 1);
                leanh::lean_inc(v_snd_2359_);
                leanh::lean_dec(v_a_2355_);
                if v_isShared_2358_ == 0 {
                    leanh::lean_ctor_set(v___x_2357_, 0, v_snd_2359_);
                    v___x_2361_ = v___x_2357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_snd_2359_);
                    v___x_2361_ = v_reuseFailAlloc_2362_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2361_;
            }
            3 => {
                if v_isShared_2367_ == 0 {
                    v___x_2369_ = v___x_2366_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2369_;
            }
            5 => {
                if v_isShared_2375_ == 0 {
                    v___x_2377_ = v___x_2374_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
                    v___x_2377_ = v_reuseFailAlloc_2378_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length___boxed(
    mut v_00_u03c3s_2380_: *mut leanh::LeanObject,
    mut v_a_2381_: *mut leanh::LeanObject,
    mut v_a_2382_: *mut leanh::LeanObject,
    mut v_a_2383_: *mut leanh::LeanObject,
    mut v_a_2384_: *mut leanh::LeanObject,
    mut v_a_2385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(
        v_00_u03c3s_2380_,
        v_a_2381_,
        v_a_2382_,
        v_a_2383_,
        v_a_2384_,
    );
    leanh::lean_dec(v_a_2384_);
    leanh::lean_dec_ref(v_a_2383_);
    leanh::lean_dec(v_a_2382_);
    leanh::lean_dec_ref(v_a_2381_);
    return v_res_2386_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(
    mut v_inst_2387_: *mut leanh::LeanObject,
    mut v_a_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
    return v___x_2394_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___boxed(
    mut v_inst_2395_: *mut leanh::LeanObject,
    mut v_a_2396_: *mut leanh::LeanObject,
    mut v___y_2397_: *mut leanh::LeanObject,
    mut v___y_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2402_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(v_inst_2395_, v_a_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
    leanh::lean_dec(v___y_2400_);
    leanh::lean_dec_ref(v___y_2399_);
    leanh::lean_dec(v___y_2398_);
    leanh::lean_dec_ref(v___y_2397_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(
    mut v_e_2403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    v___x_2404_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1;
    v___x_2405_ = leanh::lean_unsigned_to_nat(3);
    v___x_2406_ = l_Lean_Expr_isAppOfArity(v_e_2403_, v___x_2404_, v___x_2405_);
    if v___x_2406_ == 0 {
        let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2407_ = leanh::lean_box(0);
        return v___x_2407_;
    } else {
        let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2408_ = leanh::lean_box(0);
        v___x_2409_ = l_Lean_Expr_appFn_x21(v_e_2403_);
        v___x_2410_ = l_Lean_Expr_appFn_x21(v___x_2409_);
        v___x_2411_ = l_Lean_Expr_appArg_x21(v___x_2410_);
        leanh::lean_dec_ref(v___x_2410_);
        v___x_2412_ = l_Lean_Expr_appArg_x21(v___x_2409_);
        leanh::lean_dec_ref(v___x_2409_);
        v___x_2413_ = l_Lean_Expr_appArg_x21(v_e_2403_);
        v___x_2414_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2414_, 0, v___x_2412_);
        leanh::lean_ctor_set(v___x_2414_, 1, v___x_2413_);
        v___x_2415_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2415_, 0, v___x_2411_);
        leanh::lean_ctor_set(v___x_2415_, 1, v___x_2414_);
        v___x_2416_ = l_Lean_Expr_getAppFn(v_e_2403_);
        v___x_2417_ = l_Lean_Expr_constLevels_x21(v___x_2416_);
        leanh::lean_dec_ref(v___x_2416_);
        v___x_2418_ = leanh::lean_unsigned_to_nat(0);
        v___x_2419_ = l_List_get_x21Internal___redArg(v___x_2408_, v___x_2417_, v___x_2418_);
        leanh::lean_dec(v___x_2417_);
        v___x_2420_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2420_, 0, v___x_2419_);
        leanh::lean_ctor_set(v___x_2420_, 1, v___x_2415_);
        v___x_2421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2421_, 0, v___x_2420_);
        return v___x_2421_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f___boxed(
    mut v_e_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_2422_);
    leanh::lean_dec_ref(v_e_2422_);
    return v_res_2423_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2427_ = leanh::lean_box(0);
    v___x_2428_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1;
    v___x_2429_ = l_Lean_Expr_const___override(v___x_2428_, v___x_2427_);
    return v___x_2429_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2430_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2,
    );
    v___x_2431_ = leanh::lean_box(0);
    v___x_2432_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2432_, 0, v___x_2431_);
    leanh::lean_ctor_set(v___x_2432_, 1, v___x_2430_);
    leanh::lean_ctor_set(v___x_2432_, 2, v___x_2430_);
    leanh::lean_ctor_set(v___x_2432_, 3, v___x_2430_);
    return v___x_2432_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default()
-> *mut leanh::LeanObject {
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3,
    );
    return v___x_2433_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal()
-> *mut leanh::LeanObject {
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2434_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default;
    return v___x_2434_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(
    mut v_expr_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: u8 = 0;
    v___x_2443_ = l_Lean_Expr_consumeMData(v_expr_2442_);
    v___x_2444_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2;
    v___x_2445_ = leanh::lean_unsigned_to_nat(3);
    v___x_2446_ = l_Lean_Expr_isAppOfArity(v___x_2443_, v___x_2444_, v___x_2445_);
    if v___x_2446_ == 0 {
        let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_2443_);
        v___x_2447_ = leanh::lean_box(0);
        return v___x_2447_;
    } else {
        let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2448_ = leanh::lean_box(0);
        v___x_2449_ = l_Lean_Expr_appFn_x21(v___x_2443_);
        v___x_2450_ = l_Lean_Expr_appFn_x21(v___x_2449_);
        v___x_2451_ = l_Lean_Expr_appArg_x21(v___x_2450_);
        leanh::lean_dec_ref(v___x_2450_);
        v___x_2452_ = l_Lean_Expr_appArg_x21(v___x_2449_);
        leanh::lean_dec_ref(v___x_2449_);
        v___x_2453_ = l_Lean_Expr_appArg_x21(v___x_2443_);
        leanh::lean_dec_ref(v___x_2443_);
        v___x_2454_ = l_Lean_Expr_getAppFn_x27(v_expr_2442_);
        v___x_2455_ = l_Lean_Expr_constLevels_x21(v___x_2454_);
        leanh::lean_dec_ref(v___x_2454_);
        v___x_2456_ = leanh::lean_unsigned_to_nat(0);
        v___x_2457_ = l_List_get_x21Internal___redArg(v___x_2448_, v___x_2455_, v___x_2456_);
        leanh::lean_dec(v___x_2455_);
        v___x_2458_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_2458_, 0, v___x_2457_);
        leanh::lean_ctor_set(v___x_2458_, 1, v___x_2451_);
        leanh::lean_ctor_set(v___x_2458_, 2, v___x_2452_);
        leanh::lean_ctor_set(v___x_2458_, 3, v___x_2453_);
        v___x_2459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2459_, 0, v___x_2458_);
        return v___x_2459_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___boxed(
    mut v_expr_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_expr_2460_);
    leanh::lean_dec_ref(v_expr_2460_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(
    mut v_e_2462_: *mut leanh::LeanObject,
    mut v___y_2463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_unused_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = l_Lean_Expr_hasMVar(v_e_2462_);
                if v___x_2465_ == 0 {
                    v___x_2466_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2466_, 0, v_e_2462_);
                    return v___x_2466_;
                } else {
                    v___x_2467_ = lean_st_ref_get(v___y_2463_);
                    v_mctx_2468_ = leanh::lean_ctor_get(v___x_2467_, 0);
                    leanh::lean_inc_ref(v_mctx_2468_);
                    leanh::lean_dec(v___x_2467_);
                    v___x_2469_ = l_Lean_instantiateMVarsCore(v_mctx_2468_, v_e_2462_);
                    v_fst_2470_ = leanh::lean_ctor_get(v___x_2469_, 0);
                    leanh::lean_inc(v_fst_2470_);
                    v_snd_2471_ = leanh::lean_ctor_get(v___x_2469_, 1);
                    leanh::lean_inc(v_snd_2471_);
                    leanh::lean_dec_ref(v___x_2469_);
                    v___x_2472_ = lean_st_ref_take(v___y_2463_);
                    v_cache_2473_ = leanh::lean_ctor_get(v___x_2472_, 1);
                    v_zetaDeltaFVarIds_2474_ = leanh::lean_ctor_get(v___x_2472_, 2);
                    v_postponed_2475_ = leanh::lean_ctor_get(v___x_2472_, 3);
                    v_diag_2476_ = leanh::lean_ctor_get(v___x_2472_, 4);
                    v_isSharedCheck_2485_ = (!leanh::lean_is_exclusive(v___x_2472_)) as u8;
                    if v_isSharedCheck_2485_ == 0 {
                        v_unused_2486_ = leanh::lean_ctor_get(v___x_2472_, 0);
                        leanh::lean_dec(v_unused_2486_);
                        v___x_2478_ = v___x_2472_;
                        v_isShared_2479_ = v_isSharedCheck_2485_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_2476_);
                        leanh::lean_inc(v_postponed_2475_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_2474_);
                        leanh::lean_inc(v_cache_2473_);
                        leanh::lean_dec(v___x_2472_);
                        v___x_2478_ = leanh::lean_box(0);
                        v_isShared_2479_ = v_isSharedCheck_2485_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2479_ == 0 {
                    leanh::lean_ctor_set(v___x_2478_, 0, v_snd_2471_);
                    v___x_2481_ = v___x_2478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2484_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_snd_2471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_cache_2473_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2484_,
                        2,
                        v_zetaDeltaFVarIds_2474_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 3, v_postponed_2475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2484_, 4, v_diag_2476_);
                    v___x_2481_ = v_reuseFailAlloc_2484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2482_ = lean_st_ref_set(v___y_2463_, v___x_2481_);
                v___x_2483_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2483_, 0, v_fst_2470_);
                return v___x_2483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg___boxed(
    mut v_e_2487_: *mut leanh::LeanObject,
    mut v___y_2488_: *mut leanh::LeanObject,
    mut v___y_2489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2490_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(
            v_e_2487_,
            v___y_2488_,
        );
    leanh::lean_dec(v___y_2488_);
    return v_res_2490_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(
    mut v_e_2491_: *mut leanh::LeanObject,
    mut v___y_2492_: *mut leanh::LeanObject,
    mut v___y_2493_: *mut leanh::LeanObject,
    mut v___y_2494_: *mut leanh::LeanObject,
    mut v___y_2495_: *mut leanh::LeanObject,
    mut v___y_2496_: *mut leanh::LeanObject,
    mut v___y_2497_: *mut leanh::LeanObject,
    mut v___y_2498_: *mut leanh::LeanObject,
    mut v___y_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2501_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(
            v_e_2491_,
            v___y_2497_,
        );
    return v___x_2501_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___boxed(
    mut v_e_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
    mut v___y_2504_: *mut leanh::LeanObject,
    mut v___y_2505_: *mut leanh::LeanObject,
    mut v___y_2506_: *mut leanh::LeanObject,
    mut v___y_2507_: *mut leanh::LeanObject,
    mut v___y_2508_: *mut leanh::LeanObject,
    mut v___y_2509_: *mut leanh::LeanObject,
    mut v___y_2510_: *mut leanh::LeanObject,
    mut v___y_2511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(
            v_e_2502_,
            v___y_2503_,
            v___y_2504_,
            v___y_2505_,
            v___y_2506_,
            v___y_2507_,
            v___y_2508_,
            v___y_2509_,
            v___y_2510_,
        );
    leanh::lean_dec(v___y_2510_);
    leanh::lean_dec_ref(v___y_2509_);
    leanh::lean_dec(v___y_2508_);
    leanh::lean_dec_ref(v___y_2507_);
    leanh::lean_dec(v___y_2506_);
    leanh::lean_dec_ref(v___y_2505_);
    leanh::lean_dec(v___y_2504_);
    leanh::lean_dec_ref(v___y_2503_);
    return v_res_2512_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(
    mut v_msgData_2513_: *mut leanh::LeanObject,
    mut v___y_2514_: *mut leanh::LeanObject,
    mut v___y_2515_: *mut leanh::LeanObject,
    mut v___y_2516_: *mut leanh::LeanObject,
    mut v___y_2517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2519_ = lean_st_ref_get(v___y_2517_);
    v_env_2520_ = leanh::lean_ctor_get(v___x_2519_, 0);
    leanh::lean_inc_ref(v_env_2520_);
    leanh::lean_dec(v___x_2519_);
    v___x_2521_ = lean_st_ref_get(v___y_2515_);
    v_mctx_2522_ = leanh::lean_ctor_get(v___x_2521_, 0);
    leanh::lean_inc_ref(v_mctx_2522_);
    leanh::lean_dec(v___x_2521_);
    v_lctx_2523_ = leanh::lean_ctor_get(v___y_2514_, 2);
    v_options_2524_ = leanh::lean_ctor_get(v___y_2516_, 2);
    leanh::lean_inc_ref(v_options_2524_);
    leanh::lean_inc_ref(v_lctx_2523_);
    v___x_2525_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2525_, 0, v_env_2520_);
    leanh::lean_ctor_set(v___x_2525_, 1, v_mctx_2522_);
    leanh::lean_ctor_set(v___x_2525_, 2, v_lctx_2523_);
    leanh::lean_ctor_set(v___x_2525_, 3, v_options_2524_);
    v___x_2526_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2526_, 0, v___x_2525_);
    leanh::lean_ctor_set(v___x_2526_, 1, v_msgData_2513_);
    v___x_2527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2527_, 0, v___x_2526_);
    return v___x_2527_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1___boxed(
    mut v_msgData_2528_: *mut leanh::LeanObject,
    mut v___y_2529_: *mut leanh::LeanObject,
    mut v___y_2530_: *mut leanh::LeanObject,
    mut v___y_2531_: *mut leanh::LeanObject,
    mut v___y_2532_: *mut leanh::LeanObject,
    mut v___y_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msgData_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
    leanh::lean_dec(v___y_2532_);
    leanh::lean_dec_ref(v___y_2531_);
    leanh::lean_dec(v___y_2530_);
    leanh::lean_dec_ref(v___y_2529_);
    return v_res_2534_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(
    mut v_msg_2535_: *mut leanh::LeanObject,
    mut v___y_2536_: *mut leanh::LeanObject,
    mut v___y_2537_: *mut leanh::LeanObject,
    mut v___y_2538_: *mut leanh::LeanObject,
    mut v___y_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2541_ = leanh::lean_ctor_get(v___y_2538_, 5);
                v___x_2542_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
                v_a_2543_ = leanh::lean_ctor_get(v___x_2542_, 0);
                v_isSharedCheck_2551_ = (!leanh::lean_is_exclusive(v___x_2542_)) as u8;
                if v_isSharedCheck_2551_ == 0 {
                    v___x_2545_ = v___x_2542_;
                    v_isShared_2546_ = v_isSharedCheck_2551_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2543_);
                    leanh::lean_dec(v___x_2542_);
                    v___x_2545_ = leanh::lean_box(0);
                    v_isShared_2546_ = v_isSharedCheck_2551_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2541_);
                v___x_2547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2547_, 0, v_ref_2541_);
                leanh::lean_ctor_set(v___x_2547_, 1, v_a_2543_);
                if v_isShared_2546_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2545_, 1);
                    leanh::lean_ctor_set(v___x_2545_, 0, v___x_2547_);
                    v___x_2549_ = v___x_2545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2550_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
                    v___x_2549_ = v_reuseFailAlloc_2550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2549_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg___boxed(
    mut v_msg_2552_: *mut leanh::LeanObject,
    mut v___y_2553_: *mut leanh::LeanObject,
    mut v___y_2554_: *mut leanh::LeanObject,
    mut v___y_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
    mut v___y_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2558_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(
            v_msg_2552_,
            v___y_2553_,
            v___y_2554_,
            v___y_2555_,
            v___y_2556_,
        );
    leanh::lean_dec(v___y_2556_);
    leanh::lean_dec_ref(v___y_2555_);
    leanh::lean_dec(v___y_2554_);
    leanh::lean_dec_ref(v___y_2553_);
    return v_res_2558_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2560_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0;
    v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
    return v___x_2561_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
    mut v_a_2562_: *mut leanh::LeanObject,
    mut v_a_2563_: *mut leanh::LeanObject,
    mut v_a_2564_: *mut leanh::LeanObject,
    mut v_a_2565_: *mut leanh::LeanObject,
    mut v_a_2566_: *mut leanh::LeanObject,
    mut v_a_2567_: *mut leanh::LeanObject,
    mut v_a_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_a_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2592_: u8 = 0;
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2596_: u8 = 0;
    let mut v_a_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2571_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_2563_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_,
                );
                if leanh::lean_obj_tag(v___x_2571_) == 0 {
                    v_a_2572_ = leanh::lean_ctor_get(v___x_2571_, 0);
                    leanh::lean_inc_n(v_a_2572_, 2);
                    leanh::lean_dec_ref_known(v___x_2571_, 1);
                    v___x_2573_ = l_Lean_MVarId_getType(
                        v_a_2572_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_,
                    );
                    if leanh::lean_obj_tag(v___x_2573_) == 0 {
                        v_a_2574_ = leanh::lean_ctor_get(v___x_2573_, 0);
                        leanh::lean_inc(v_a_2574_);
                        leanh::lean_dec_ref_known(v___x_2573_, 1);
                        v___x_2575_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_a_2574_, v_a_2567_);
                        v_a_2576_ = leanh::lean_ctor_get(v___x_2575_, 0);
                        v_isSharedCheck_2588_ =
                            (!leanh::lean_is_exclusive(v___x_2575_)) as u8;
                        if v_isSharedCheck_2588_ == 0 {
                            v___x_2578_ = v___x_2575_;
                            v_isShared_2579_ = v_isSharedCheck_2588_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2576_);
                            leanh::lean_dec(v___x_2575_);
                            v___x_2578_ = leanh::lean_box(0);
                            v_isShared_2579_ = v_isSharedCheck_2588_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_2572_);
                        v_a_2589_ = leanh::lean_ctor_get(v___x_2573_, 0);
                        v_isSharedCheck_2596_ =
                            (!leanh::lean_is_exclusive(v___x_2573_)) as u8;
                        if v_isSharedCheck_2596_ == 0 {
                            v___x_2591_ = v___x_2573_;
                            v_isShared_2592_ = v_isSharedCheck_2596_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2589_);
                            leanh::lean_dec(v___x_2573_);
                            v___x_2591_ = leanh::lean_box(0);
                            v_isShared_2592_ = v_isSharedCheck_2596_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2597_ = leanh::lean_ctor_get(v___x_2571_, 0);
                    v_isSharedCheck_2604_ = (!leanh::lean_is_exclusive(v___x_2571_)) as u8;
                    if v_isSharedCheck_2604_ == 0 {
                        v___x_2599_ = v___x_2571_;
                        v_isShared_2600_ = v_isSharedCheck_2604_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2597_);
                        leanh::lean_dec(v___x_2571_);
                        v___x_2599_ = leanh::lean_box(0);
                        v_isShared_2600_ = v_isSharedCheck_2604_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2580_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2576_);
                leanh::lean_dec(v_a_2576_);
                if leanh::lean_obj_tag(v___x_2580_) == 1 {
                    v_val_2581_ = leanh::lean_ctor_get(v___x_2580_, 0);
                    leanh::lean_inc(v_val_2581_);
                    leanh::lean_dec_ref_known(v___x_2580_, 1);
                    v___x_2582_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2582_, 0, v_a_2572_);
                    leanh::lean_ctor_set(v___x_2582_, 1, v_val_2581_);
                    if v_isShared_2579_ == 0 {
                        leanh::lean_ctor_set(v___x_2578_, 0, v___x_2582_);
                        v___x_2584_ = v___x_2578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2585_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
                        v___x_2584_ = v_reuseFailAlloc_2585_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2580_);
                    leanh::lean_del_object(v___x_2578_);
                    leanh::lean_dec(v_a_2572_);
                    v___x_2586_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1,
                    );
                    v___x_2587_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(v___x_2586_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
                    return v___x_2587_;
                }
            }
            2 => {
                return v___x_2584_;
            }
            3 => {
                if v_isShared_2592_ == 0 {
                    v___x_2594_ = v___x_2591_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2595_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
                    v___x_2594_ = v_reuseFailAlloc_2595_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2594_;
            }
            5 => {
                if v_isShared_2600_ == 0 {
                    v___x_2602_ = v___x_2599_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2603_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
                    v___x_2602_ = v_reuseFailAlloc_2603_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2602_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___boxed(
    mut v_a_2605_: *mut leanh::LeanObject,
    mut v_a_2606_: *mut leanh::LeanObject,
    mut v_a_2607_: *mut leanh::LeanObject,
    mut v_a_2608_: *mut leanh::LeanObject,
    mut v_a_2609_: *mut leanh::LeanObject,
    mut v_a_2610_: *mut leanh::LeanObject,
    mut v_a_2611_: *mut leanh::LeanObject,
    mut v_a_2612_: *mut leanh::LeanObject,
    mut v_a_2613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2614_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
        v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_,
    );
    leanh::lean_dec(v_a_2612_);
    leanh::lean_dec_ref(v_a_2611_);
    leanh::lean_dec(v_a_2610_);
    leanh::lean_dec_ref(v_a_2609_);
    leanh::lean_dec(v_a_2608_);
    leanh::lean_dec_ref(v_a_2607_);
    leanh::lean_dec(v_a_2606_);
    leanh::lean_dec_ref(v_a_2605_);
    return v_res_2614_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(
    mut v_00_u03b1_2615_: *mut leanh::LeanObject,
    mut v_msg_2616_: *mut leanh::LeanObject,
    mut v___y_2617_: *mut leanh::LeanObject,
    mut v___y_2618_: *mut leanh::LeanObject,
    mut v___y_2619_: *mut leanh::LeanObject,
    mut v___y_2620_: *mut leanh::LeanObject,
    mut v___y_2621_: *mut leanh::LeanObject,
    mut v___y_2622_: *mut leanh::LeanObject,
    mut v___y_2623_: *mut leanh::LeanObject,
    mut v___y_2624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(
            v_msg_2616_,
            v___y_2621_,
            v___y_2622_,
            v___y_2623_,
            v___y_2624_,
        );
    return v___x_2626_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___boxed(
    mut v_00_u03b1_2627_: *mut leanh::LeanObject,
    mut v_msg_2628_: *mut leanh::LeanObject,
    mut v___y_2629_: *mut leanh::LeanObject,
    mut v___y_2630_: *mut leanh::LeanObject,
    mut v___y_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
    mut v___y_2633_: *mut leanh::LeanObject,
    mut v___y_2634_: *mut leanh::LeanObject,
    mut v___y_2635_: *mut leanh::LeanObject,
    mut v___y_2636_: *mut leanh::LeanObject,
    mut v___y_2637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2638_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(
        v_00_u03b1_2627_,
        v_msg_2628_,
        v___y_2629_,
        v___y_2630_,
        v___y_2631_,
        v___y_2632_,
        v___y_2633_,
        v___y_2634_,
        v___y_2635_,
        v___y_2636_,
    );
    leanh::lean_dec(v___y_2636_);
    leanh::lean_dec_ref(v___y_2635_);
    leanh::lean_dec(v___y_2634_);
    leanh::lean_dec_ref(v___y_2633_);
    leanh::lean_dec(v___y_2632_);
    leanh::lean_dec_ref(v___y_2631_);
    leanh::lean_dec(v___y_2630_);
    leanh::lean_dec_ref(v___y_2629_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(
    mut v_goal_2645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_u_2646_ = leanh::lean_ctor_get(v_goal_2645_, 0);
    leanh::lean_inc(v_u_2646_);
    v_00_u03c3s_2647_ = leanh::lean_ctor_get(v_goal_2645_, 1);
    leanh::lean_inc_ref(v_00_u03c3s_2647_);
    v_hyps_2648_ = leanh::lean_ctor_get(v_goal_2645_, 2);
    leanh::lean_inc_ref(v_hyps_2648_);
    v_target_2649_ = leanh::lean_ctor_get(v_goal_2645_, 3);
    leanh::lean_inc_ref(v_target_2649_);
    leanh::lean_dec_ref(v_goal_2645_);
    v___x_2650_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1;
    v___x_2651_ = leanh::lean_box(0);
    v___x_2652_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2652_, 0, v_u_2646_);
    leanh::lean_ctor_set(v___x_2652_, 1, v___x_2651_);
    v___x_2653_ = l_Lean_mkConst(v___x_2650_, v___x_2652_);
    v___x_2654_ = l_Lean_mkApp3(v___x_2653_, v_00_u03c3s_2647_, v_hyps_2648_, v_target_2649_);
    return v___x_2654_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(
    mut v_goal_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_u_2656_ = leanh::lean_ctor_get(v_goal_2655_, 0);
    leanh::lean_inc(v_u_2656_);
    v_00_u03c3s_2657_ = leanh::lean_ctor_get(v_goal_2655_, 1);
    leanh::lean_inc_ref(v_00_u03c3s_2657_);
    v_hyps_2658_ = leanh::lean_ctor_get(v_goal_2655_, 2);
    leanh::lean_inc_ref(v_hyps_2658_);
    v_target_2659_ = leanh::lean_ctor_get(v_goal_2655_, 3);
    leanh::lean_inc_ref(v_target_2659_);
    leanh::lean_dec_ref(v_goal_2655_);
    v___x_2660_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2;
    v___x_2661_ = leanh::lean_box(0);
    v___x_2662_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2662_, 0, v_u_2656_);
    leanh::lean_ctor_set(v___x_2662_, 1, v___x_2661_);
    v___x_2663_ = l_Lean_mkConst(v___x_2660_, v___x_2662_);
    v___x_2664_ = l_Lean_mkApp3(v___x_2663_, v_00_u03c3s_2657_, v_hyps_2658_, v_target_2659_);
    return v___x_2664_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(
    mut v_msg_2665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2666_ = leanh::lean_box(0);
    v___x_2667_ = lean_panic_fn_borrowed(v___x_2666_, v_msg_2665_);
    return v___x_2667_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2;
    v___x_2672_ = leanh::lean_unsigned_to_nat(8);
    v___x_2673_ = leanh::lean_unsigned_to_nat(141);
    v___x_2674_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1;
    v___x_2675_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0;
    v___x_2676_ = l_mkPanicMessageWithDecl(
        v___x_2675_,
        v___x_2674_,
        v___x_2673_,
        v___x_2672_,
        v___x_2671_,
    );
    return v___x_2676_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(
    mut v_name_2677_: *mut leanh::LeanObject,
    mut v_e_2678_: *mut leanh::LeanObject,
    mut v_p_2679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v_name_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_2678_);
                v___x_2680_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_2678_);
                if leanh::lean_obj_tag(v___x_2680_) == 1 {
                    leanh::lean_dec_ref(v_e_2678_);
                    v_val_2681_ = leanh::lean_ctor_get(v___x_2680_, 0);
                    v_isSharedCheck_2692_ = (!leanh::lean_is_exclusive(v___x_2680_)) as u8;
                    if v_isSharedCheck_2692_ == 0 {
                        v___x_2683_ = v___x_2680_;
                        v_isShared_2684_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2681_);
                        leanh::lean_dec(v___x_2680_);
                        v___x_2683_ = leanh::lean_box(0);
                        v_isShared_2684_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2680_);
                    v___x_2693_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_2678_);
                    if leanh::lean_obj_tag(v___x_2693_) == 1 {
                        leanh::lean_dec_ref(v_e_2678_);
                        v_val_2694_ = leanh::lean_ctor_get(v___x_2693_, 0);
                        leanh::lean_inc(v_val_2694_);
                        leanh::lean_dec_ref_known(v___x_2693_, 1);
                        v_snd_2695_ = leanh::lean_ctor_get(v_val_2694_, 1);
                        leanh::lean_inc(v_snd_2695_);
                        leanh::lean_dec(v_val_2694_);
                        v_snd_2696_ = leanh::lean_ctor_get(v_snd_2695_, 1);
                        leanh::lean_inc(v_snd_2696_);
                        leanh::lean_dec(v_snd_2695_);
                        v_fst_2697_ = leanh::lean_ctor_get(v_snd_2696_, 0);
                        leanh::lean_inc(v_fst_2697_);
                        v_snd_2698_ = leanh::lean_ctor_get(v_snd_2696_, 1);
                        leanh::lean_inc(v_snd_2698_);
                        leanh::lean_dec(v_snd_2696_);
                        v___x_2699_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_p_2679_);
                        v___x_2700_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_2677_, v_snd_2698_, v___x_2699_);
                        if leanh::lean_obj_tag(v___x_2700_) == 0 {
                            v___x_2701_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_p_2679_);
                            leanh::lean_dec(v_p_2679_);
                            v_e_2678_ = v_fst_2697_;
                            v_p_2679_ = v___x_2701_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_fst_2697_);
                            leanh::lean_dec(v_p_2679_);
                            return v___x_2700_;
                        }
                    } else {
                        leanh::lean_dec(v___x_2693_);
                        leanh::lean_dec(v_p_2679_);
                        v___x_2703_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_2678_);
                        if leanh::lean_obj_tag(v___x_2703_) == 1 {
                            leanh::lean_dec_ref_known(v___x_2703_, 1);
                            v___x_2704_ = leanh::lean_box(0);
                            return v___x_2704_;
                        } else {
                            leanh::lean_dec(v___x_2703_);
                            v___x_2705_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3);
                            v___x_2706_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(v___x_2705_);
                            return v___x_2706_;
                        }
                    }
                }
            }
            1 => {
                v_name_2685_ = leanh::lean_ctor_get(v_val_2681_, 0);
                v___x_2686_ = lean_name_eq(v_name_2685_, v_name_2677_);
                if v___x_2686_ == 0 {
                    leanh::lean_del_object(v___x_2683_);
                    leanh::lean_dec(v_val_2681_);
                    leanh::lean_dec(v_p_2679_);
                    v___x_2687_ = leanh::lean_box(0);
                    return v___x_2687_;
                } else {
                    v___x_2688_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2688_, 0, v_p_2679_);
                    leanh::lean_ctor_set(v___x_2688_, 1, v_val_2681_);
                    if v_isShared_2684_ == 0 {
                        leanh::lean_ctor_set(v___x_2683_, 0, v___x_2688_);
                        v___x_2690_ = v___x_2683_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2691_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
                        v___x_2690_ = v_reuseFailAlloc_2691_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___boxed(
    mut v_name_2707_: *mut leanh::LeanObject,
    mut v_e_2708_: *mut leanh::LeanObject,
    mut v_p_2709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2710_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_2707_, v_e_2708_, v_p_2709_);
    leanh::lean_dec(v_name_2707_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(
    mut v_goal_2711_: *mut leanh::LeanObject,
    mut v_name_2712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hyps_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hyps_2713_ = leanh::lean_ctor_get(v_goal_2711_, 2);
    leanh::lean_inc_ref(v_hyps_2713_);
    leanh::lean_dec_ref(v_goal_2711_);
    v___x_2714_ = l_Lean_SubExpr_Pos_root;
    v___x_2715_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_2712_, v_hyps_2713_, v___x_2714_);
    return v___x_2715_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f___boxed(
    mut v_goal_2716_: *mut leanh::LeanObject,
    mut v_name_2717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_2716_, v_name_2717_);
    leanh::lean_dec(v_name_2717_);
    return v_res_2718_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(
    mut v_msg_2719_: *mut leanh::LeanObject,
    mut v___y_2720_: *mut leanh::LeanObject,
    mut v___y_2721_: *mut leanh::LeanObject,
    mut v___y_2722_: *mut leanh::LeanObject,
    mut v___y_2723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2730_: u8 = 0;
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2725_ = leanh::lean_ctor_get(v___y_2722_, 5);
                v___x_2726_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
                v_a_2727_ = leanh::lean_ctor_get(v___x_2726_, 0);
                v_isSharedCheck_2735_ = (!leanh::lean_is_exclusive(v___x_2726_)) as u8;
                if v_isSharedCheck_2735_ == 0 {
                    v___x_2729_ = v___x_2726_;
                    v_isShared_2730_ = v_isSharedCheck_2735_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2727_);
                    leanh::lean_dec(v___x_2726_);
                    v___x_2729_ = leanh::lean_box(0);
                    v_isShared_2730_ = v_isSharedCheck_2735_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2725_);
                v___x_2731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2731_, 0, v_ref_2725_);
                leanh::lean_ctor_set(v___x_2731_, 1, v_a_2727_);
                if v_isShared_2730_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2729_, 1);
                    leanh::lean_ctor_set(v___x_2729_, 0, v___x_2731_);
                    v___x_2733_ = v___x_2729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2734_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
                    v___x_2733_ = v_reuseFailAlloc_2734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg___boxed(
    mut v_msg_2736_: *mut leanh::LeanObject,
    mut v___y_2737_: *mut leanh::LeanObject,
    mut v___y_2738_: *mut leanh::LeanObject,
    mut v___y_2739_: *mut leanh::LeanObject,
    mut v___y_2740_: *mut leanh::LeanObject,
    mut v___y_2741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2742_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(
            v_msg_2736_,
            v___y_2737_,
            v___y_2738_,
            v___y_2739_,
            v___y_2740_,
        );
    leanh::lean_dec(v___y_2740_);
    leanh::lean_dec_ref(v___y_2739_);
    leanh::lean_dec(v___y_2738_);
    leanh::lean_dec_ref(v___y_2737_);
    return v_res_2742_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(
    mut v___y_2750_: u8,
    mut v_suppressElabErrors_2751_: u8,
    mut v_x_2752_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2752_) == 1 {
        let mut v_pre_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2753_ = leanh::lean_ctor_get(v_x_2752_, 0);
        match leanh::lean_obj_tag(v_pre_2753_) {
            1 => {
                let mut v_pre_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_2754_ = leanh::lean_ctor_get(v_pre_2753_, 0);
                match leanh::lean_obj_tag(v_pre_2754_) {
                    0 => {
                        let mut v_str_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2758_: u8 = 0;
                        v_str_2755_ = leanh::lean_ctor_get(v_x_2752_, 1);
                        v_str_2756_ = leanh::lean_ctor_get(v_pre_2753_, 1);
                        v___x_2757_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_2758_ = lean_string_dec_eq(v_str_2756_, v___x_2757_);
                        if v___x_2758_ == 0 {
                            let mut v___x_2759_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2760_: u8 = 0;
                            v___x_2759_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0;
                            v___x_2760_ = lean_string_dec_eq(v_str_2756_, v___x_2759_);
                            if v___x_2760_ == 0 {
                                return v___y_2750_;
                            } else {
                                let mut v___x_2761_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2762_: u8 = 0;
                                v___x_2761_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1;
                                v___x_2762_ = lean_string_dec_eq(v_str_2755_, v___x_2761_);
                                if v___x_2762_ == 0 {
                                    return v___y_2750_;
                                } else {
                                    return v_suppressElabErrors_2751_;
                                }
                            }
                        } else {
                            let mut v___x_2763_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2764_: u8 = 0;
                            v___x_2763_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2;
                            v___x_2764_ = lean_string_dec_eq(v_str_2755_, v___x_2763_);
                            if v___x_2764_ == 0 {
                                return v___y_2750_;
                            } else {
                                return v_suppressElabErrors_2751_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2765_ = leanh::lean_ctor_get(v_pre_2754_, 0);
                        if leanh::lean_obj_tag(v_pre_2765_) == 0 {
                            let mut v_str_2766_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2767_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2768_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2769_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2770_: u8 = 0;
                            v_str_2766_ = leanh::lean_ctor_get(v_x_2752_, 1);
                            v_str_2767_ = leanh::lean_ctor_get(v_pre_2753_, 1);
                            v_str_2768_ = leanh::lean_ctor_get(v_pre_2754_, 1);
                            v___x_2769_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3;
                            v___x_2770_ = lean_string_dec_eq(v_str_2768_, v___x_2769_);
                            if v___x_2770_ == 0 {
                                return v___y_2750_;
                            } else {
                                let mut v___x_2771_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2772_: u8 = 0;
                                v___x_2771_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4;
                                v___x_2772_ = lean_string_dec_eq(v_str_2767_, v___x_2771_);
                                if v___x_2772_ == 0 {
                                    return v___y_2750_;
                                } else {
                                    let mut v___x_2773_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2774_: u8 = 0;
                                    v___x_2773_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5;
                                    v___x_2774_ = lean_string_dec_eq(v_str_2766_, v___x_2773_);
                                    if v___x_2774_ == 0 {
                                        return v___y_2750_;
                                    } else {
                                        return v_suppressElabErrors_2751_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2750_;
                        }
                    }
                    _ => {
                        return v___y_2750_;
                    }
                }
            }
            0 => {
                let mut v_str_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2777_: u8 = 0;
                v_str_2775_ = leanh::lean_ctor_get(v_x_2752_, 1);
                v___x_2776_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6;
                v___x_2777_ = lean_string_dec_eq(v_str_2775_, v___x_2776_);
                if v___x_2777_ == 0 {
                    return v___y_2750_;
                } else {
                    return v_suppressElabErrors_2751_;
                }
            }
            _ => {
                return v___y_2750_;
            }
        }
    } else {
        return v___y_2750_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed(
    mut v___y_2778_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2779_: *mut leanh::LeanObject,
    mut v_x_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4449__boxed_2781_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2782_: u8 = 0;
    let mut v_res_2783_: u8 = 0;
    let mut v_r_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_4449__boxed_2781_ = (leanh::lean_unbox(v___y_2778_) as u8);
    v_suppressElabErrors_boxed_2782_ = (leanh::lean_unbox(v_suppressElabErrors_2779_) as u8);
    v_res_2783_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(v___y_4449__boxed_2781_, v_suppressElabErrors_boxed_2782_, v_x_2780_);
    leanh::lean_dec(v_x_2780_);
    v_r_2784_ = leanh::lean_box((v_res_2783_) as usize);
    return v_r_2784_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(
    mut v_opts_2785_: *mut leanh::LeanObject,
    mut v_opt_2786_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_2787_ = leanh::lean_ctor_get(v_opt_2786_, 0);
    v_defValue_2788_ = leanh::lean_ctor_get(v_opt_2786_, 1);
    v_map_2789_ = leanh::lean_ctor_get(v_opts_2785_, 0);
    v___x_2790_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2789_,
            v_name_2787_,
        );
    if leanh::lean_obj_tag(v___x_2790_) == 0 {
        let mut v___x_2791_: u8 = 0;
        v___x_2791_ = (leanh::lean_unbox(v_defValue_2788_) as u8);
        return v___x_2791_;
    } else {
        let mut v_val_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2792_ = leanh::lean_ctor_get(v___x_2790_, 0);
        leanh::lean_inc(v_val_2792_);
        leanh::lean_dec_ref_known(v___x_2790_, 1);
        if leanh::lean_obj_tag(v_val_2792_) == 1 {
            let mut v_v_2793_: u8 = 0;
            v_v_2793_ = leanh::lean_ctor_get_uint8(v_val_2792_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_2792_, 0);
            return v_v_2793_;
        } else {
            let mut v___x_2794_: u8 = 0;
            leanh::lean_dec(v_val_2792_);
            v___x_2794_ = (leanh::lean_unbox(v_defValue_2788_) as u8);
            return v___x_2794_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_opts_2795_: *mut leanh::LeanObject,
    mut v_opt_2796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2797_: u8 = 0;
    let mut v_r_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2797_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_opts_2795_, v_opt_2796_);
    leanh::lean_dec_ref(v_opt_2796_);
    leanh::lean_dec_ref(v_opts_2795_);
    v_r_2798_ = leanh::lean_box((v_res_2797_) as usize);
    return v_r_2798_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(
    mut v_ref_2800_: *mut leanh::LeanObject,
    mut v_msgData_2801_: *mut leanh::LeanObject,
    mut v_severity_2802_: u8,
    mut v_isSilent_2803_: u8,
    mut v___y_2804_: *mut leanh::LeanObject,
    mut v___y_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: u8 = 0;
    let mut v___y_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: u8 = 0;
    let mut v___y_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v___y_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2847_: u8 = 0;
    let mut v___y_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2849_: u8 = 0;
    let mut v___y_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2851_: u8 = 0;
    let mut v___y_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2859_: u8 = 0;
    let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v___y_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: u8 = 0;
    let mut v___y_2875_: u8 = 0;
    let mut v___y_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2877_: u8 = 0;
    let mut v___y_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: u8 = 0;
    let mut v___y_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: u8 = 0;
    let mut v___y_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: u8 = 0;
    let mut v_ref_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    let mut v___y_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2897_: u8 = 0;
    let mut v___y_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2900_: u8 = 0;
    let mut v___y_2901_: u8 = 0;
    let mut v___y_2903_: u8 = 0;
    let mut v_fileName_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2908_: u8 = 0;
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2893_ = 2;
                v___x_2918_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2802_, v___x_2893_);
                if v___x_2918_ == 0 {
                    v___y_2903_ = v___x_2918_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2801_);
                    v___x_2919_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2801_);
                    v___y_2903_ = v___x_2919_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2819_ = lean_st_ref_take(v___y_2818_);
                v_currNamespace_2820_ = leanh::lean_ctor_get(v___y_2817_, 6);
                v_openDecls_2821_ = leanh::lean_ctor_get(v___y_2817_, 7);
                v_env_2822_ = leanh::lean_ctor_get(v___x_2819_, 0);
                v_nextMacroScope_2823_ = leanh::lean_ctor_get(v___x_2819_, 1);
                v_ngen_2824_ = leanh::lean_ctor_get(v___x_2819_, 2);
                v_auxDeclNGen_2825_ = leanh::lean_ctor_get(v___x_2819_, 3);
                v_traceState_2826_ = leanh::lean_ctor_get(v___x_2819_, 4);
                v_cache_2827_ = leanh::lean_ctor_get(v___x_2819_, 5);
                v_messages_2828_ = leanh::lean_ctor_get(v___x_2819_, 6);
                v_infoState_2829_ = leanh::lean_ctor_get(v___x_2819_, 7);
                v_snapshotTasks_2830_ = leanh::lean_ctor_get(v___x_2819_, 8);
                v_isSharedCheck_2844_ = (!leanh::lean_is_exclusive(v___x_2819_)) as u8;
                if v_isSharedCheck_2844_ == 0 {
                    v___x_2832_ = v___x_2819_;
                    v_isShared_2833_ = v_isSharedCheck_2844_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2830_);
                    leanh::lean_inc(v_infoState_2829_);
                    leanh::lean_inc(v_messages_2828_);
                    leanh::lean_inc(v_cache_2827_);
                    leanh::lean_inc(v_traceState_2826_);
                    leanh::lean_inc(v_auxDeclNGen_2825_);
                    leanh::lean_inc(v_ngen_2824_);
                    leanh::lean_inc(v_nextMacroScope_2823_);
                    leanh::lean_inc(v_env_2822_);
                    leanh::lean_dec(v___x_2819_);
                    v___x_2832_ = leanh::lean_box(0);
                    v_isShared_2833_ = v_isSharedCheck_2844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_2821_);
                leanh::lean_inc(v_currNamespace_2820_);
                v___x_2834_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2834_, 0, v_currNamespace_2820_);
                leanh::lean_ctor_set(v___x_2834_, 1, v_openDecls_2821_);
                v___x_2835_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2835_, 0, v___x_2834_);
                leanh::lean_ctor_set(v___x_2835_, 1, v___y_2812_);
                leanh::lean_inc_ref(v___y_2811_);
                leanh::lean_inc_ref(v___y_2814_);
                v___x_2836_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2836_, 0, v___y_2814_);
                leanh::lean_ctor_set(v___x_2836_, 1, v___y_2810_);
                leanh::lean_ctor_set(v___x_2836_, 2, v___y_2816_);
                leanh::lean_ctor_set(v___x_2836_, 3, v___y_2811_);
                leanh::lean_ctor_set(v___x_2836_, 4, v___x_2835_);
                leanh::lean_ctor_set_uint8(
                    v___x_2836_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2813_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2836_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2815_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2836_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2803_,
                );
                v___x_2837_ = l_Lean_MessageLog_add(v___x_2836_, v_messages_2828_);
                if v_isShared_2833_ == 0 {
                    leanh::lean_ctor_set(v___x_2832_, 6, v___x_2837_);
                    v___x_2839_ = v___x_2832_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_env_2822_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_nextMacroScope_2823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_ngen_2824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_auxDeclNGen_2825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_traceState_2826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 5, v_cache_2827_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 6, v___x_2837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 7, v_infoState_2829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 8, v_snapshotTasks_2830_);
                    v___x_2839_ = v_reuseFailAlloc_2843_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2840_ = lean_st_ref_set(v___y_2818_, v___x_2839_);
                v___x_2841_ = leanh::lean_box(0);
                v___x_2842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2842_, 0, v___x_2841_);
                return v___x_2842_;
            }
            4 => {
                v___x_2854_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2801_,
                    );
                v___x_2855_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v___x_2854_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
                v_a_2856_ = leanh::lean_ctor_get(v___x_2855_, 0);
                v_isSharedCheck_2869_ = (!leanh::lean_is_exclusive(v___x_2855_)) as u8;
                if v_isSharedCheck_2869_ == 0 {
                    v___x_2858_ = v___x_2855_;
                    v_isShared_2859_ = v_isSharedCheck_2869_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2856_);
                    leanh::lean_dec(v___x_2855_);
                    v___x_2858_ = leanh::lean_box(0);
                    v_isShared_2859_ = v_isSharedCheck_2869_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_2848_, 2);
                v___x_2860_ = l_Lean_FileMap_toPosition(v___y_2848_, v___y_2852_);
                leanh::lean_dec(v___y_2852_);
                v___x_2861_ = l_Lean_FileMap_toPosition(v___y_2848_, v___y_2853_);
                leanh::lean_dec(v___y_2853_);
                v___x_2862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2862_, 0, v___x_2861_);
                v___x_2863_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0;
                if v___y_2847_ == 0 {
                    leanh::lean_del_object(v___x_2858_);
                    leanh::lean_dec_ref(v___y_2846_);
                    v___y_2810_ = v___x_2860_;
                    v___y_2811_ = v___x_2863_;
                    v___y_2812_ = v_a_2856_;
                    v___y_2813_ = v___y_2849_;
                    v___y_2814_ = v___y_2850_;
                    v___y_2815_ = v___y_2851_;
                    v___y_2816_ = v___x_2862_;
                    v___y_2817_ = v___y_2806_;
                    v___y_2818_ = v___y_2807_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2856_);
                    v___x_2864_ = l_Lean_MessageData_hasTag(v___y_2846_, v_a_2856_);
                    if v___x_2864_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2862_, 1);
                        leanh::lean_dec_ref(v___x_2860_);
                        leanh::lean_dec(v_a_2856_);
                        v___x_2865_ = leanh::lean_box(0);
                        if v_isShared_2859_ == 0 {
                            leanh::lean_ctor_set(v___x_2858_, 0, v___x_2865_);
                            v___x_2867_ = v___x_2858_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2868_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
                            v___x_2867_ = v_reuseFailAlloc_2868_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2858_);
                        v___y_2810_ = v___x_2860_;
                        v___y_2811_ = v___x_2863_;
                        v___y_2812_ = v_a_2856_;
                        v___y_2813_ = v___y_2849_;
                        v___y_2814_ = v___y_2850_;
                        v___y_2815_ = v___y_2851_;
                        v___y_2816_ = v___x_2862_;
                        v___y_2817_ = v___y_2806_;
                        v___y_2818_ = v___y_2807_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2867_;
            }
            7 => {
                v___x_2879_ = l_Lean_Syntax_getTailPos_x3f(v___y_2872_, v___y_2875_);
                leanh::lean_dec(v___y_2872_);
                if leanh::lean_obj_tag(v___x_2879_) == 0 {
                    leanh::lean_inc(v___y_2878_);
                    v___y_2846_ = v___y_2871_;
                    v___y_2847_ = v___y_2874_;
                    v___y_2848_ = v___y_2873_;
                    v___y_2849_ = v___y_2875_;
                    v___y_2850_ = v___y_2876_;
                    v___y_2851_ = v___y_2877_;
                    v___y_2852_ = v___y_2878_;
                    v___y_2853_ = v___y_2878_;
                    state = 4;
                    continue;
                } else {
                    v_val_2880_ = leanh::lean_ctor_get(v___x_2879_, 0);
                    leanh::lean_inc(v_val_2880_);
                    leanh::lean_dec_ref_known(v___x_2879_, 1);
                    v___y_2846_ = v___y_2871_;
                    v___y_2847_ = v___y_2874_;
                    v___y_2848_ = v___y_2873_;
                    v___y_2849_ = v___y_2875_;
                    v___y_2850_ = v___y_2876_;
                    v___y_2851_ = v___y_2877_;
                    v___y_2852_ = v___y_2878_;
                    v___y_2853_ = v_val_2880_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2889_ = l_Lean_replaceRef(v_ref_2800_, v___y_2887_);
                v___x_2890_ = l_Lean_Syntax_getPos_x3f(v_ref_2889_, v___y_2885_);
                if leanh::lean_obj_tag(v___x_2890_) == 0 {
                    v___x_2891_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2871_ = v___y_2882_;
                    v___y_2872_ = v_ref_2889_;
                    v___y_2873_ = v___y_2884_;
                    v___y_2874_ = v___y_2883_;
                    v___y_2875_ = v___y_2885_;
                    v___y_2876_ = v___y_2886_;
                    v___y_2877_ = v___y_2888_;
                    v___y_2878_ = v___x_2891_;
                    state = 7;
                    continue;
                } else {
                    v_val_2892_ = leanh::lean_ctor_get(v___x_2890_, 0);
                    leanh::lean_inc(v_val_2892_);
                    leanh::lean_dec_ref_known(v___x_2890_, 1);
                    v___y_2871_ = v___y_2882_;
                    v___y_2872_ = v_ref_2889_;
                    v___y_2873_ = v___y_2884_;
                    v___y_2874_ = v___y_2883_;
                    v___y_2875_ = v___y_2885_;
                    v___y_2876_ = v___y_2886_;
                    v___y_2877_ = v___y_2888_;
                    v___y_2878_ = v_val_2892_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2901_ == 0 {
                    v___y_2882_ = v___y_2895_;
                    v___y_2883_ = v___y_2897_;
                    v___y_2884_ = v___y_2896_;
                    v___y_2885_ = v___y_2900_;
                    v___y_2886_ = v___y_2898_;
                    v___y_2887_ = v___y_2899_;
                    v___y_2888_ = v_severity_2802_;
                    state = 8;
                    continue;
                } else {
                    v___y_2882_ = v___y_2895_;
                    v___y_2883_ = v___y_2897_;
                    v___y_2884_ = v___y_2896_;
                    v___y_2885_ = v___y_2900_;
                    v___y_2886_ = v___y_2898_;
                    v___y_2887_ = v___y_2899_;
                    v___y_2888_ = v___x_2893_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2903_ == 0 {
                    v_fileName_2904_ = leanh::lean_ctor_get(v___y_2806_, 0);
                    v_fileMap_2905_ = leanh::lean_ctor_get(v___y_2806_, 1);
                    v_options_2906_ = leanh::lean_ctor_get(v___y_2806_, 2);
                    v_ref_2907_ = leanh::lean_ctor_get(v___y_2806_, 5);
                    v_suppressElabErrors_2908_ = leanh::lean_ctor_get_uint8(
                        v___y_2806_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2909_ = leanh::lean_box((v___y_2903_) as usize);
                    v___x_2910_ = leanh::lean_box((v_suppressElabErrors_2908_) as usize);
                    v___f_2911_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2911_, 0, v___x_2909_);
                    leanh::lean_closure_set(v___f_2911_, 1, v___x_2910_);
                    v___x_2912_ = 1;
                    v___x_2913_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2802_, v___x_2912_);
                    if v___x_2913_ == 0 {
                        v___y_2895_ = v___f_2911_;
                        v___y_2896_ = v_fileMap_2905_;
                        v___y_2897_ = v_suppressElabErrors_2908_;
                        v___y_2898_ = v_fileName_2904_;
                        v___y_2899_ = v_ref_2907_;
                        v___y_2900_ = v___y_2903_;
                        v___y_2901_ = v___x_2913_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2914_ = l_Lean_warningAsError;
                        v___x_2915_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_options_2906_, v___x_2914_);
                        v___y_2895_ = v___f_2911_;
                        v___y_2896_ = v_fileMap_2905_;
                        v___y_2897_ = v_suppressElabErrors_2908_;
                        v___y_2898_ = v_fileName_2904_;
                        v___y_2899_ = v_ref_2907_;
                        v___y_2900_ = v___y_2903_;
                        v___y_2901_ = v___x_2915_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2801_);
                    v___x_2916_ = leanh::lean_box(0);
                    v___x_2917_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2917_, 0, v___x_2916_);
                    return v___x_2917_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___boxed(
    mut v_ref_2920_: *mut leanh::LeanObject,
    mut v_msgData_2921_: *mut leanh::LeanObject,
    mut v_severity_2922_: *mut leanh::LeanObject,
    mut v_isSilent_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
    mut v___y_2925_: *mut leanh::LeanObject,
    mut v___y_2926_: *mut leanh::LeanObject,
    mut v___y_2927_: *mut leanh::LeanObject,
    mut v___y_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2929_: u8 = 0;
    let mut v_isSilent_boxed_2930_: u8 = 0;
    let mut v_res_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2929_ = (leanh::lean_unbox(v_severity_2922_) as u8);
    v_isSilent_boxed_2930_ = (leanh::lean_unbox(v_isSilent_2923_) as u8);
    v_res_2931_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_2920_, v_msgData_2921_, v_severity_boxed_2929_, v_isSilent_boxed_2930_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
    leanh::lean_dec(v___y_2927_);
    leanh::lean_dec_ref(v___y_2926_);
    leanh::lean_dec(v___y_2925_);
    leanh::lean_dec_ref(v___y_2924_);
    leanh::lean_dec(v_ref_2920_);
    return v_res_2931_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(
    mut v_msgData_2932_: *mut leanh::LeanObject,
    mut v_severity_2933_: u8,
    mut v_isSilent_2934_: u8,
    mut v___y_2935_: *mut leanh::LeanObject,
    mut v___y_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2940_ = leanh::lean_ctor_get(v___y_2937_, 5);
    v___x_2941_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_2940_, v_msgData_2932_, v_severity_2933_, v_isSilent_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0___boxed(
    mut v_msgData_2942_: *mut leanh::LeanObject,
    mut v_severity_2943_: *mut leanh::LeanObject,
    mut v_isSilent_2944_: *mut leanh::LeanObject,
    mut v___y_2945_: *mut leanh::LeanObject,
    mut v___y_2946_: *mut leanh::LeanObject,
    mut v___y_2947_: *mut leanh::LeanObject,
    mut v___y_2948_: *mut leanh::LeanObject,
    mut v___y_2949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2950_: u8 = 0;
    let mut v_isSilent_boxed_2951_: u8 = 0;
    let mut v_res_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2950_ = (leanh::lean_unbox(v_severity_2943_) as u8);
    v_isSilent_boxed_2951_ = (leanh::lean_unbox(v_isSilent_2944_) as u8);
    v_res_2952_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_2942_, v_severity_boxed_2950_, v_isSilent_boxed_2951_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
    leanh::lean_dec(v___y_2948_);
    leanh::lean_dec_ref(v___y_2947_);
    leanh::lean_dec(v___y_2946_);
    leanh::lean_dec_ref(v___y_2945_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(
    mut v_msgData_2953_: *mut leanh::LeanObject,
    mut v___y_2954_: *mut leanh::LeanObject,
    mut v___y_2955_: *mut leanh::LeanObject,
    mut v___y_2956_: *mut leanh::LeanObject,
    mut v___y_2957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = 1;
    v___x_2960_ = 0;
    v___x_2961_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_2953_, v___x_2959_, v___x_2960_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
    return v___x_2961_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0___boxed(
    mut v_msgData_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
    mut v___y_2964_: *mut leanh::LeanObject,
    mut v___y_2965_: *mut leanh::LeanObject,
    mut v___y_2966_: *mut leanh::LeanObject,
    mut v___y_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(
        v_msgData_2962_,
        v___y_2963_,
        v___y_2964_,
        v___y_2965_,
        v___y_2966_,
    );
    leanh::lean_dec(v___y_2966_);
    leanh::lean_dec_ref(v___y_2965_);
    leanh::lean_dec(v___y_2964_);
    leanh::lean_dec_ref(v___y_2963_);
    return v_res_2968_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2970_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0;
    v___x_2971_ = l_Lean_stringToMessageData(v___x_2970_);
    return v___x_2971_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2;
    v___x_2974_ = l_Lean_stringToMessageData(v___x_2973_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4;
    v___x_2977_ = l_Lean_stringToMessageData(v___x_2976_);
    return v___x_2977_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2979_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6;
    v___x_2980_ = l_Lean_stringToMessageData(v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2982_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8;
    v___x_2983_ = l_Lean_stringToMessageData(v___x_2982_);
    return v___x_2983_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(
    mut v_expr_2984_: *mut leanh::LeanObject,
    mut v_expectedType_2985_: *mut leanh::LeanObject,
    mut v_suppressWarning_2986_: u8,
    mut v_a_2987_: *mut leanh::LeanObject,
    mut v_a_2988_: *mut leanh::LeanObject,
    mut v_a_2989_: *mut leanh::LeanObject,
    mut v_a_2990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: u8 = 0;
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut v_a_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3007_ = 0;
                leanh::lean_inc_ref(v_expr_2984_);
                v___x_3008_ = l_Lean_Meta_check(
                    v_expr_2984_,
                    v___x_3007_,
                    v_a_2987_,
                    v_a_2988_,
                    v_a_2989_,
                    v_a_2990_,
                );
                if leanh::lean_obj_tag(v___x_3008_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3008_, 1);
                    leanh::lean_inc_ref(v_expectedType_2985_);
                    v___x_3009_ = l_Lean_Meta_check(
                        v_expectedType_2985_,
                        v___x_3007_,
                        v_a_2987_,
                        v_a_2988_,
                        v_a_2989_,
                        v_a_2990_,
                    );
                    if leanh::lean_obj_tag(v___x_3009_) == 0 {
                        leanh::lean_dec_ref_known(v___x_3009_, 1);
                        leanh::lean_inc(v_a_2990_);
                        leanh::lean_inc_ref(v_a_2989_);
                        leanh::lean_inc(v_a_2988_);
                        leanh::lean_inc_ref(v_a_2987_);
                        leanh::lean_inc_ref(v_expr_2984_);
                        v___x_3010_ = lean_infer_type(
                            v_expr_2984_,
                            v_a_2987_,
                            v_a_2988_,
                            v_a_2989_,
                            v_a_2990_,
                        );
                        if leanh::lean_obj_tag(v___x_3010_) == 0 {
                            v_a_3011_ = leanh::lean_ctor_get(v___x_3010_, 0);
                            leanh::lean_inc_n(v_a_3011_, 2);
                            leanh::lean_dec_ref_known(v___x_3010_, 1);
                            leanh::lean_inc_ref(v_expectedType_2985_);
                            v___x_3012_ = l_Lean_Meta_isExprDefEqGuarded(
                                v_a_3011_,
                                v_expectedType_2985_,
                                v_a_2987_,
                                v_a_2988_,
                                v_a_2989_,
                                v_a_2990_,
                            );
                            if leanh::lean_obj_tag(v___x_3012_) == 0 {
                                v_a_3013_ = leanh::lean_ctor_get(v___x_3012_, 0);
                                leanh::lean_inc(v_a_3013_);
                                leanh::lean_dec_ref_known(v___x_3012_, 1);
                                v___x_3014_ = (leanh::lean_unbox(v_a_3013_) as u8);
                                leanh::lean_dec(v_a_3013_);
                                if v___x_3014_ == 0 {
                                    v___x_3015_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5);
                                    v___x_3016_ = l_Lean_indentExpr(v_expr_2984_);
                                    v___x_3017_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3017_, 0, v___x_3015_);
                                    leanh::lean_ctor_set(v___x_3017_, 1, v___x_3016_);
                                    v___x_3018_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7);
                                    v___x_3019_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3017_);
                                    leanh::lean_ctor_set(v___x_3019_, 1, v___x_3018_);
                                    v___x_3020_ = l_Lean_indentExpr(v_a_3011_);
                                    v___x_3021_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3021_, 0, v___x_3019_);
                                    leanh::lean_ctor_set(v___x_3021_, 1, v___x_3020_);
                                    v___x_3022_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9);
                                    v___x_3023_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3023_, 0, v___x_3021_);
                                    leanh::lean_ctor_set(v___x_3023_, 1, v___x_3022_);
                                    v___x_3024_ = l_Lean_indentExpr(v_expectedType_2985_);
                                    v___x_3025_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3025_, 0, v___x_3023_);
                                    leanh::lean_ctor_set(v___x_3025_, 1, v___x_3024_);
                                    v___x_3026_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_3025_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
                                    return v___x_3026_;
                                } else {
                                    leanh::lean_dec(v_a_3011_);
                                    v___y_2993_ = v_a_2987_;
                                    v___y_2994_ = v_a_2988_;
                                    v___y_2995_ = v_a_2989_;
                                    v___y_2996_ = v_a_2990_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_3011_);
                                leanh::lean_dec_ref(v_expectedType_2985_);
                                leanh::lean_dec_ref(v_expr_2984_);
                                v_a_3027_ = leanh::lean_ctor_get(v___x_3012_, 0);
                                v_isSharedCheck_3034_ =
                                    (!leanh::lean_is_exclusive(v___x_3012_)) as u8;
                                if v_isSharedCheck_3034_ == 0 {
                                    v___x_3029_ = v___x_3012_;
                                    v_isShared_3030_ = v_isSharedCheck_3034_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3027_);
                                    leanh::lean_dec(v___x_3012_);
                                    v___x_3029_ = leanh::lean_box(0);
                                    v_isShared_3030_ = v_isSharedCheck_3034_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_expectedType_2985_);
                            leanh::lean_dec_ref(v_expr_2984_);
                            v_a_3035_ = leanh::lean_ctor_get(v___x_3010_, 0);
                            v_isSharedCheck_3042_ =
                                (!leanh::lean_is_exclusive(v___x_3010_)) as u8;
                            if v_isSharedCheck_3042_ == 0 {
                                v___x_3037_ = v___x_3010_;
                                v_isShared_3038_ = v_isSharedCheck_3042_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3035_);
                                leanh::lean_dec(v___x_3010_);
                                v___x_3037_ = leanh::lean_box(0);
                                v_isShared_3038_ = v_isSharedCheck_3042_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_expectedType_2985_);
                        leanh::lean_dec_ref(v_expr_2984_);
                        return v___x_3009_;
                    }
                } else {
                    leanh::lean_dec_ref(v_expectedType_2985_);
                    leanh::lean_dec_ref(v_expr_2984_);
                    return v___x_3008_;
                }
            }
            1 => {
                if v_suppressWarning_2986_ == 0 {
                    v___x_2997_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1,
                    );
                    v___x_2998_ = l_Lean_MessageData_ofExpr(v_expr_2984_);
                    v___x_2999_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2999_, 0, v___x_2997_);
                    leanh::lean_ctor_set(v___x_2999_, 1, v___x_2998_);
                    v___x_3000_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3,
                    );
                    v___x_3001_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3001_, 0, v___x_2999_);
                    leanh::lean_ctor_set(v___x_3001_, 1, v___x_3000_);
                    v___x_3002_ = l_Lean_MessageData_ofExpr(v_expectedType_2985_);
                    v___x_3003_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3003_, 0, v___x_3001_);
                    leanh::lean_ctor_set(v___x_3003_, 1, v___x_3002_);
                    v___x_3004_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v___x_3003_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
                    return v___x_3004_;
                } else {
                    leanh::lean_dec_ref(v_expectedType_2985_);
                    leanh::lean_dec_ref(v_expr_2984_);
                    v___x_3005_ = leanh::lean_box(0);
                    v___x_3006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3006_, 0, v___x_3005_);
                    return v___x_3006_;
                }
            }
            2 => {
                if v_isShared_3030_ == 0 {
                    v___x_3032_ = v___x_3029_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
                    v___x_3032_ = v_reuseFailAlloc_3033_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3032_;
            }
            4 => {
                if v_isShared_3038_ == 0 {
                    v___x_3040_ = v___x_3037_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
                    v___x_3040_ = v_reuseFailAlloc_3041_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___boxed(
    mut v_expr_3043_: *mut leanh::LeanObject,
    mut v_expectedType_3044_: *mut leanh::LeanObject,
    mut v_suppressWarning_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
    mut v_a_3047_: *mut leanh::LeanObject,
    mut v_a_3048_: *mut leanh::LeanObject,
    mut v_a_3049_: *mut leanh::LeanObject,
    mut v_a_3050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_suppressWarning_boxed_3051_: u8 = 0;
    let mut v_res_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_suppressWarning_boxed_3051_ = (leanh::lean_unbox(v_suppressWarning_3045_) as u8);
    v_res_3052_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(
        v_expr_3043_,
        v_expectedType_3044_,
        v_suppressWarning_boxed_3051_,
        v_a_3046_,
        v_a_3047_,
        v_a_3048_,
        v_a_3049_,
    );
    leanh::lean_dec(v_a_3049_);
    leanh::lean_dec_ref(v_a_3048_);
    leanh::lean_dec(v_a_3047_);
    leanh::lean_dec_ref(v_a_3046_);
    return v_res_3052_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(
    mut v_00_u03b1_3053_: *mut leanh::LeanObject,
    mut v_msg_3054_: *mut leanh::LeanObject,
    mut v___y_3055_: *mut leanh::LeanObject,
    mut v___y_3056_: *mut leanh::LeanObject,
    mut v___y_3057_: *mut leanh::LeanObject,
    mut v___y_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(
            v_msg_3054_,
            v___y_3055_,
            v___y_3056_,
            v___y_3057_,
            v___y_3058_,
        );
    return v___x_3060_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___boxed(
    mut v_00_u03b1_3061_: *mut leanh::LeanObject,
    mut v_msg_3062_: *mut leanh::LeanObject,
    mut v___y_3063_: *mut leanh::LeanObject,
    mut v___y_3064_: *mut leanh::LeanObject,
    mut v___y_3065_: *mut leanh::LeanObject,
    mut v___y_3066_: *mut leanh::LeanObject,
    mut v___y_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(
        v_00_u03b1_3061_,
        v_msg_3062_,
        v___y_3063_,
        v___y_3064_,
        v___y_3065_,
        v___y_3066_,
    );
    leanh::lean_dec(v___y_3066_);
    leanh::lean_dec_ref(v___y_3065_);
    leanh::lean_dec(v___y_3064_);
    leanh::lean_dec_ref(v___y_3063_);
    return v_res_3068_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(
    mut v_goal_3069_: *mut leanh::LeanObject,
    mut v_prf_3070_: *mut leanh::LeanObject,
    mut v_suppressWarning_3071_: u8,
    mut v_a_3072_: *mut leanh::LeanObject,
    mut v_a_3073_: *mut leanh::LeanObject,
    mut v_a_3074_: *mut leanh::LeanObject,
    mut v_a_3075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3077_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_3069_);
    v___x_3078_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(
        v_prf_3070_,
        v___x_3077_,
        v_suppressWarning_3071_,
        v_a_3072_,
        v_a_3073_,
        v_a_3074_,
        v_a_3075_,
    );
    return v___x_3078_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof___boxed(
    mut v_goal_3079_: *mut leanh::LeanObject,
    mut v_prf_3080_: *mut leanh::LeanObject,
    mut v_suppressWarning_3081_: *mut leanh::LeanObject,
    mut v_a_3082_: *mut leanh::LeanObject,
    mut v_a_3083_: *mut leanh::LeanObject,
    mut v_a_3084_: *mut leanh::LeanObject,
    mut v_a_3085_: *mut leanh::LeanObject,
    mut v_a_3086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_suppressWarning_boxed_3087_: u8 = 0;
    let mut v_res_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_suppressWarning_boxed_3087_ = (leanh::lean_unbox(v_suppressWarning_3081_) as u8);
    v_res_3088_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(
        v_goal_3079_,
        v_prf_3080_,
        v_suppressWarning_boxed_3087_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
    );
    leanh::lean_dec(v_a_3085_);
    leanh::lean_dec_ref(v_a_3084_);
    leanh::lean_dec(v_a_3083_);
    leanh::lean_dec_ref(v_a_3082_);
    return v_res_3088_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
    mut v_x_3100_: *mut leanh::LeanObject,
    mut v_a_3101_: *mut leanh::LeanObject,
    mut v_a_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_a_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut v_a_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3104_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2;
                leanh::lean_inc(v_x_3100_);
                v___x_3105_ = l_Lean_Syntax_isOfKind(v_x_3100_, v___x_3104_);
                if v___x_3105_ == 0 {
                    v___x_3106_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4;
                    v___x_3107_ = l_Lean_Core_mkFreshUserName(v___x_3106_, v_a_3101_, v_a_3102_);
                    if leanh::lean_obj_tag(v___x_3107_) == 0 {
                        v_a_3108_ = leanh::lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3116_ =
                            (!leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3116_ == 0 {
                            v___x_3110_ = v___x_3107_;
                            v_isShared_3111_ = v_isSharedCheck_3116_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3108_);
                            leanh::lean_dec(v___x_3107_);
                            v___x_3110_ = leanh::lean_box(0);
                            v_isShared_3111_ = v_isSharedCheck_3116_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_x_3100_);
                        v_a_3117_ = leanh::lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3124_ =
                            (!leanh::lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3124_ == 0 {
                            v___x_3119_ = v___x_3107_;
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3117_);
                            leanh::lean_dec(v___x_3107_);
                            v___x_3119_ = leanh::lean_box(0);
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3125_ = leanh::lean_unsigned_to_nat(0);
                    v_name_3126_ = l_Lean_Syntax_getArg(v_x_3100_, v___x_3125_);
                    v___x_3127_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6;
                    leanh::lean_inc(v_name_3126_);
                    v___x_3128_ = l_Lean_Syntax_isOfKind(v_name_3126_, v___x_3127_);
                    if v___x_3128_ == 0 {
                        leanh::lean_dec(v_name_3126_);
                        v___x_3129_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4;
                        v___x_3130_ =
                            l_Lean_Core_mkFreshUserName(v___x_3129_, v_a_3101_, v_a_3102_);
                        if leanh::lean_obj_tag(v___x_3130_) == 0 {
                            v_a_3131_ = leanh::lean_ctor_get(v___x_3130_, 0);
                            v_isSharedCheck_3139_ =
                                (!leanh::lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3139_ == 0 {
                                v___x_3133_ = v___x_3130_;
                                v_isShared_3134_ = v_isSharedCheck_3139_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3131_);
                                leanh::lean_dec(v___x_3130_);
                                v___x_3133_ = leanh::lean_box(0);
                                v_isShared_3134_ = v_isSharedCheck_3139_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_x_3100_);
                            v_a_3140_ = leanh::lean_ctor_get(v___x_3130_, 0);
                            v_isSharedCheck_3147_ =
                                (!leanh::lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3147_ == 0 {
                                v___x_3142_ = v___x_3130_;
                                v_isShared_3143_ = v_isSharedCheck_3147_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3140_);
                                leanh::lean_dec(v___x_3130_);
                                v___x_3142_ = leanh::lean_box(0);
                                v_isShared_3143_ = v_isSharedCheck_3147_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_x_3100_);
                        v___x_3148_ = l_Lean_TSyntax_getId(v_name_3126_);
                        v___x_3149_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3149_, 0, v___x_3148_);
                        leanh::lean_ctor_set(v___x_3149_, 1, v_name_3126_);
                        v___x_3150_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3150_, 0, v___x_3149_);
                        return v___x_3150_;
                    }
                }
            }
            1 => {
                v___x_3112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3112_, 0, v_a_3108_);
                leanh::lean_ctor_set(v___x_3112_, 1, v_x_3100_);
                if v_isShared_3111_ == 0 {
                    leanh::lean_ctor_set(v___x_3110_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3114_;
            }
            3 => {
                if v_isShared_3120_ == 0 {
                    v___x_3122_ = v___x_3119_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3122_;
            }
            5 => {
                v___x_3135_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3135_, 0, v_a_3131_);
                leanh::lean_ctor_set(v___x_3135_, 1, v_x_3100_);
                if v_isShared_3134_ == 0 {
                    leanh::lean_ctor_set(v___x_3133_, 0, v___x_3135_);
                    v___x_3137_ = v___x_3133_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3138_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
                    v___x_3137_ = v_reuseFailAlloc_3138_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3137_;
            }
            7 => {
                if v_isShared_3143_ == 0 {
                    v___x_3145_ = v___x_3142_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3146_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
                    v___x_3145_ = v_reuseFailAlloc_3146_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___boxed(
    mut v_x_3151_: *mut leanh::LeanObject,
    mut v_a_3152_: *mut leanh::LeanObject,
    mut v_a_3153_: *mut leanh::LeanObject,
    mut v_a_3154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3155_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_x_3151_, v_a_3152_, v_a_3153_);
    leanh::lean_dec(v_a_3153_);
    leanh::lean_dec_ref(v_a_3152_);
    return v_res_3155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(
    mut v_as_3156_: *mut leanh::LeanObject,
    mut v_i_3157_: usize,
    mut v_stop_3158_: usize,
    mut v_b_3159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3160_: u8 = 0;
    let mut v___x_3161_: usize = 0;
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3160_ = lean_usize_dec_eq(v_i_3157_, v_stop_3158_);
                if v___x_3160_ == 0 {
                    v___x_3161_ = 1usize;
                    v___x_3162_ = lean_usize_sub(v_i_3157_, v___x_3161_);
                    v___x_3163_ = lean_array_uget_borrowed(v_as_3156_, v___x_3162_);
                    v_snd_3164_ = leanh::lean_ctor_get(v___x_3163_, 1);
                    v_fst_3165_ = leanh::lean_ctor_get(v___x_3163_, 0);
                    v_fst_3166_ = leanh::lean_ctor_get(v_snd_3164_, 0);
                    v_snd_3167_ = leanh::lean_ctor_get(v_snd_3164_, 1);
                    v___x_3168_ = (leanh::lean_unbox(v_snd_3167_) as u8);
                    leanh::lean_inc(v_fst_3166_);
                    leanh::lean_inc(v_fst_3165_);
                    v___x_3169_ = l_Lean_Expr_lam___override(
                        v_fst_3165_,
                        v_fst_3166_,
                        v_b_3159_,
                        v___x_3168_,
                    );
                    v_i_3157_ = v___x_3162_;
                    v_b_3159_ = v___x_3169_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3159_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0___boxed(
    mut v_as_3171_: *mut leanh::LeanObject,
    mut v_i_3172_: *mut leanh::LeanObject,
    mut v_stop_3173_: *mut leanh::LeanObject,
    mut v_b_3174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3175_: usize = 0;
    let mut v_stop_boxed_3176_: usize = 0;
    let mut v_res_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3175_ = leanh::lean_unbox_usize(v_i_3172_);
    leanh::lean_dec(v_i_3172_);
    v_stop_boxed_3176_ = leanh::lean_unbox_usize(v_stop_3173_);
    leanh::lean_dec(v_stop_3173_);
    v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_as_3171_, v_i_boxed_3175_, v_stop_boxed_3176_, v_b_3174_);
    leanh::lean_dec_ref(v_as_3171_);
    return v_res_3177_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(
    mut v_revLams_3178_: *mut leanh::LeanObject,
    mut v_revAppArgs_3179_: *mut leanh::LeanObject,
    mut v_body_3180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: u8 = 0;
    v___x_3181_ = 0;
    v___x_3182_ = l_Lean_Expr_betaRev(v_body_3180_, v_revAppArgs_3179_, v___x_3181_, v___x_3181_);
    v___x_3183_ = lean_array_get_size(v_revLams_3178_);
    v___x_3184_ = leanh::lean_unsigned_to_nat(0);
    v___x_3185_ = lean_nat_dec_lt(v___x_3184_, v___x_3183_);
    if v___x_3185_ == 0 {
        return v___x_3182_;
    } else {
        let mut v___x_3186_: usize = 0;
        let mut v___x_3187_: usize = 0;
        let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3186_ = lean_usize_of_nat(v___x_3183_);
        v___x_3187_ = 0usize;
        v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_revLams_3178_, v___x_3186_, v___x_3187_, v___x_3182_);
        return v___x_3188_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap___boxed(
    mut v_revLams_3189_: *mut leanh::LeanObject,
    mut v_revAppArgs_3190_: *mut leanh::LeanObject,
    mut v_body_3191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3192_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_3189_, v_revAppArgs_3190_, v_body_3191_);
    leanh::lean_dec_ref(v_revAppArgs_3190_);
    leanh::lean_dec_ref(v_revLams_3189_);
    return v_res_3192_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(
    mut v_00_u03c3s_3193_: *mut leanh::LeanObject,
    mut v_revLams_3194_: *mut leanh::LeanObject,
    mut v_revAppArgs_3195_: *mut leanh::LeanObject,
    mut v_e_3196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uniq_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3228_: u8 = 0;
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_3196_);
                v___x_3197_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_3196_);
                if leanh::lean_obj_tag(v___x_3197_) == 1 {
                    leanh::lean_dec_ref(v_e_3196_);
                    leanh::lean_dec_ref(v_revAppArgs_3195_);
                    leanh::lean_dec_ref(v_revLams_3194_);
                    v_val_3198_ = leanh::lean_ctor_get(v___x_3197_, 0);
                    leanh::lean_inc(v_val_3198_);
                    leanh::lean_dec_ref_known(v___x_3197_, 1);
                    v_fst_3199_ = leanh::lean_ctor_get(v_val_3198_, 0);
                    leanh::lean_inc(v_fst_3199_);
                    leanh::lean_dec(v_val_3198_);
                    v___x_3200_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_fst_3199_, v_00_u03c3s_3193_);
                    return v___x_3200_;
                } else {
                    leanh::lean_dec(v___x_3197_);
                    leanh::lean_inc_ref(v_e_3196_);
                    v___x_3201_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_3196_);
                    if leanh::lean_obj_tag(v___x_3201_) == 1 {
                        leanh::lean_dec_ref(v_e_3196_);
                        leanh::lean_dec_ref(v_00_u03c3s_3193_);
                        v_val_3202_ = leanh::lean_ctor_get(v___x_3201_, 0);
                        leanh::lean_inc(v_val_3202_);
                        leanh::lean_dec_ref_known(v___x_3201_, 1);
                        v_name_3203_ = leanh::lean_ctor_get(v_val_3202_, 0);
                        v_uniq_3204_ = leanh::lean_ctor_get(v_val_3202_, 1);
                        v_p_3205_ = leanh::lean_ctor_get(v_val_3202_, 2);
                        v_isSharedCheck_3214_ =
                            (!leanh::lean_is_exclusive(v_val_3202_)) as u8;
                        if v_isSharedCheck_3214_ == 0 {
                            v___x_3207_ = v_val_3202_;
                            v_isShared_3208_ = v_isSharedCheck_3214_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_p_3205_);
                            leanh::lean_inc(v_uniq_3204_);
                            leanh::lean_inc(v_name_3203_);
                            leanh::lean_dec(v_val_3202_);
                            v___x_3207_ = leanh::lean_box(0);
                            v_isShared_3208_ = v_isSharedCheck_3214_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3201_);
                        v___x_3215_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_3196_);
                        if leanh::lean_obj_tag(v___x_3215_) == 1 {
                            leanh::lean_dec_ref(v_e_3196_);
                            v_val_3216_ = leanh::lean_ctor_get(v___x_3215_, 0);
                            leanh::lean_inc(v_val_3216_);
                            leanh::lean_dec_ref_known(v___x_3215_, 1);
                            v_snd_3217_ = leanh::lean_ctor_get(v_val_3216_, 1);
                            v_snd_3218_ = leanh::lean_ctor_get(v_snd_3217_, 1);
                            leanh::lean_inc(v_snd_3218_);
                            v_fst_3219_ = leanh::lean_ctor_get(v_val_3216_, 0);
                            leanh::lean_inc(v_fst_3219_);
                            leanh::lean_dec(v_val_3216_);
                            v_fst_3220_ = leanh::lean_ctor_get(v_snd_3218_, 0);
                            leanh::lean_inc(v_fst_3220_);
                            v_snd_3221_ = leanh::lean_ctor_get(v_snd_3218_, 1);
                            leanh::lean_inc(v_snd_3221_);
                            leanh::lean_dec(v_snd_3218_);
                            leanh::lean_inc_ref(v_revAppArgs_3195_);
                            leanh::lean_inc_ref(v_revLams_3194_);
                            leanh::lean_inc_ref_n(v_00_u03c3s_3193_, 2);
                            v___x_3222_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_3193_, v_revLams_3194_, v_revAppArgs_3195_, v_fst_3220_);
                            v___x_3223_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_3193_, v_revLams_3194_, v_revAppArgs_3195_, v_snd_3221_);
                            v___x_3224_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                                v_fst_3219_,
                                v_00_u03c3s_3193_,
                                v___x_3222_,
                                v___x_3223_,
                            );
                            return v___x_3224_;
                        } else {
                            leanh::lean_dec(v___x_3215_);
                            if leanh::lean_obj_tag(v_e_3196_) == 6 {
                                v_binderName_3225_ = leanh::lean_ctor_get(v_e_3196_, 0);
                                leanh::lean_inc(v_binderName_3225_);
                                v_binderType_3226_ = leanh::lean_ctor_get(v_e_3196_, 1);
                                leanh::lean_inc_ref(v_binderType_3226_);
                                v_body_3227_ = leanh::lean_ctor_get(v_e_3196_, 2);
                                leanh::lean_inc_ref(v_body_3227_);
                                v_binderInfo_3228_ = leanh::lean_ctor_get_uint8(
                                    v_e_3196_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8)
                                        as u32,
                                );
                                leanh::lean_dec_ref_known(v_e_3196_, 3);
                                v___x_3229_ = lean_array_get_size(v_revAppArgs_3195_);
                                v___x_3230_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3231_ = lean_nat_sub(v___x_3229_, v___x_3230_);
                                v___x_3232_ = lean_nat_dec_lt(v___x_3231_, v___x_3229_);
                                if v___x_3232_ == 0 {
                                    leanh::lean_dec(v___x_3231_);
                                    v___x_3233_ =
                                        leanh::lean_box((v_binderInfo_3228_) as usize);
                                    v___x_3234_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3234_, 0, v_binderType_3226_);
                                    leanh::lean_ctor_set(v___x_3234_, 1, v___x_3233_);
                                    v___x_3235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3235_, 0, v_binderName_3225_);
                                    leanh::lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                                    v___x_3236_ = lean_array_push(v_revLams_3194_, v___x_3235_);
                                    v_revLams_3194_ = v___x_3236_;
                                    v_e_3196_ = v_body_3227_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_binderType_3226_);
                                    leanh::lean_dec(v_binderName_3225_);
                                    v___x_3238_ = lean_array_fget(v_revAppArgs_3195_, v___x_3231_);
                                    leanh::lean_dec(v___x_3231_);
                                    v___x_3239_ = lean_array_pop(v_revAppArgs_3195_);
                                    v___x_3240_ = lean_expr_instantiate1(v_body_3227_, v___x_3238_);
                                    leanh::lean_dec(v___x_3238_);
                                    leanh::lean_dec_ref(v_body_3227_);
                                    v_revAppArgs_3195_ = v___x_3239_;
                                    v_e_3196_ = v___x_3240_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                if leanh::lean_obj_tag(v_e_3196_) == 5 {
                                    v_fn_3242_ = leanh::lean_ctor_get(v_e_3196_, 0);
                                    leanh::lean_inc_ref(v_fn_3242_);
                                    v_arg_3243_ = leanh::lean_ctor_get(v_e_3196_, 1);
                                    leanh::lean_inc_ref(v_arg_3243_);
                                    leanh::lean_dec_ref_known(v_e_3196_, 2);
                                    v___x_3244_ = lean_array_push(v_revAppArgs_3195_, v_arg_3243_);
                                    v_revAppArgs_3195_ = v___x_3244_;
                                    v_e_3196_ = v_fn_3242_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_00_u03c3s_3193_);
                                    v___x_3246_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_3194_, v_revAppArgs_3195_, v_e_3196_);
                                    leanh::lean_dec_ref(v_revAppArgs_3195_);
                                    leanh::lean_dec_ref(v_revLams_3194_);
                                    return v___x_3246_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3209_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_3194_, v_revAppArgs_3195_, v_p_3205_);
                leanh::lean_dec_ref(v_revAppArgs_3195_);
                leanh::lean_dec_ref(v_revLams_3194_);
                if v_isShared_3208_ == 0 {
                    leanh::lean_ctor_set(v___x_3207_, 2, v___x_3209_);
                    v___x_3211_ = v___x_3207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3213_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_name_3203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_uniq_3204_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 2, v___x_3209_);
                    v___x_3211_ = v_reuseFailAlloc_3213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3212_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_3211_);
                return v___x_3212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(
    mut v_00_u03c3s_3249_: *mut leanh::LeanObject,
    mut v_hyps_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0;
    v___x_3252_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_3249_, v___x_3251_, v___x_3251_, v_hyps_3250_);
    return v___x_3252_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(
    mut v_00_u03c3s_x27_3253_: *mut leanh::LeanObject,
    mut v_e_3254_: *mut leanh::LeanObject,
    mut v_args_3255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_mkAppN(v_e_3254_, v_args_3255_);
    v___x_3257_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(
        v_00_u03c3s_x27_3253_,
        v___x_3256_,
    );
    return v___x_3257_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames___boxed(
    mut v_00_u03c3s_x27_3258_: *mut leanh::LeanObject,
    mut v_e_3259_: *mut leanh::LeanObject,
    mut v_args_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3261_ = l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(
        v_00_u03c3s_x27_3258_,
        v_e_3259_,
        v_args_3260_,
    );
    leanh::lean_dec_ref(v_args_3260_);
    return v_res_3261_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0;
    v___x_3264_ = l_Lean_stringToMessageData(v___x_3263_);
    return v___x_3264_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(
    mut v_upperBound_3265_: *mut leanh::LeanObject,
    mut v_a_3266_: *mut leanh::LeanObject,
    mut v_b_3267_: *mut leanh::LeanObject,
    mut v___y_3268_: *mut leanh::LeanObject,
    mut v___y_3269_: *mut leanh::LeanObject,
    mut v___y_3270_: *mut leanh::LeanObject,
    mut v___y_3271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u8 = 0;
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3278_ = lean_nat_dec_lt(v_a_3266_, v_upperBound_3265_);
                if v___x_3278_ == 0 {
                    leanh::lean_dec(v_a_3266_);
                    v___x_3279_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3279_, 0, v_b_3267_);
                    return v___x_3279_;
                } else {
                    leanh::lean_inc_ref(v_b_3267_);
                    v___x_3280_ = l_Lean_Meta_whnfR(
                        v_b_3267_,
                        v___y_3268_,
                        v___y_3269_,
                        v___y_3270_,
                        v___y_3271_,
                    );
                    if leanh::lean_obj_tag(v___x_3280_) == 0 {
                        v_a_3281_ = leanh::lean_ctor_get(v___x_3280_, 0);
                        leanh::lean_inc(v_a_3281_);
                        leanh::lean_dec_ref_known(v___x_3280_, 1);
                        v___x_3282_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1;
                        v___x_3283_ = leanh::lean_unsigned_to_nat(3);
                        v___x_3284_ = l_Lean_Expr_isAppOfArity(v_a_3281_, v___x_3282_, v___x_3283_);
                        if v___x_3284_ == 0 {
                            leanh::lean_dec(v_a_3281_);
                            v___x_3285_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1);
                            leanh::lean_inc_ref(v_b_3267_);
                            v___x_3286_ = l_Lean_MessageData_ofExpr(v_b_3267_);
                            v___x_3287_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3287_, 0, v___x_3285_);
                            leanh::lean_ctor_set(v___x_3287_, 1, v___x_3286_);
                            v___x_3288_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_3287_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
                            if leanh::lean_obj_tag(v___x_3288_) == 0 {
                                leanh::lean_dec_ref_known(v___x_3288_, 1);
                                v_a_3274_ = v_b_3267_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_3267_);
                                leanh::lean_dec(v_a_3266_);
                                v_a_3289_ = leanh::lean_ctor_get(v___x_3288_, 0);
                                v_isSharedCheck_3296_ =
                                    (!leanh::lean_is_exclusive(v___x_3288_)) as u8;
                                if v_isSharedCheck_3296_ == 0 {
                                    v___x_3291_ = v___x_3288_;
                                    v_isShared_3292_ = v_isSharedCheck_3296_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3289_);
                                    leanh::lean_dec(v___x_3288_);
                                    v___x_3291_ = leanh::lean_box(0);
                                    v_isShared_3292_ = v_isSharedCheck_3296_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_3267_);
                            v___x_3297_ = l_Lean_Expr_appArg_x21(v_a_3281_);
                            leanh::lean_dec(v_a_3281_);
                            v_a_3274_ = v___x_3297_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_3267_);
                        leanh::lean_dec(v_a_3266_);
                        return v___x_3280_;
                    }
                }
            }
            1 => {
                v___x_3275_ = leanh::lean_unsigned_to_nat(1);
                v___x_3276_ = lean_nat_add(v_a_3266_, v___x_3275_);
                leanh::lean_dec(v_a_3266_);
                v_a_3266_ = v___x_3276_;
                v_b_3267_ = v_a_3274_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3292_ == 0 {
                    v___x_3294_ = v___x_3291_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
                    v___x_3294_ = v_reuseFailAlloc_3295_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___boxed(
    mut v_upperBound_3298_: *mut leanh::LeanObject,
    mut v_a_3299_: *mut leanh::LeanObject,
    mut v_b_3300_: *mut leanh::LeanObject,
    mut v___y_3301_: *mut leanh::LeanObject,
    mut v___y_3302_: *mut leanh::LeanObject,
    mut v___y_3303_: *mut leanh::LeanObject,
    mut v___y_3304_: *mut leanh::LeanObject,
    mut v___y_3305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_3298_, v_a_3299_, v_b_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
    leanh::lean_dec(v___y_3304_);
    leanh::lean_dec_ref(v___y_3303_);
    leanh::lean_dec(v___y_3302_);
    leanh::lean_dec_ref(v___y_3301_);
    leanh::lean_dec(v_upperBound_3298_);
    return v_res_3306_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(
    mut v_00_u03c3s_3307_: *mut leanh::LeanObject,
    mut v_n_3308_: *mut leanh::LeanObject,
    mut v_a_3309_: *mut leanh::LeanObject,
    mut v_a_3310_: *mut leanh::LeanObject,
    mut v_a_3311_: *mut leanh::LeanObject,
    mut v_a_3312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = leanh::lean_unsigned_to_nat(0);
    v___x_3315_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_n_3308_, v___x_3314_, v_00_u03c3s_3307_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_dropStateList___boxed(
    mut v_00_u03c3s_3316_: *mut leanh::LeanObject,
    mut v_n_3317_: *mut leanh::LeanObject,
    mut v_a_3318_: *mut leanh::LeanObject,
    mut v_a_3319_: *mut leanh::LeanObject,
    mut v_a_3320_: *mut leanh::LeanObject,
    mut v_a_3321_: *mut leanh::LeanObject,
    mut v_a_3322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3323_ = l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(
        v_00_u03c3s_3316_,
        v_n_3317_,
        v_a_3318_,
        v_a_3319_,
        v_a_3320_,
        v_a_3321_,
    );
    leanh::lean_dec(v_a_3321_);
    leanh::lean_dec_ref(v_a_3320_);
    leanh::lean_dec(v_a_3319_);
    leanh::lean_dec_ref(v_a_3318_);
    leanh::lean_dec(v_n_3317_);
    return v_res_3323_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(
    mut v_upperBound_3324_: *mut leanh::LeanObject,
    mut v_inst_3325_: *mut leanh::LeanObject,
    mut v_R_3326_: *mut leanh::LeanObject,
    mut v_a_3327_: *mut leanh::LeanObject,
    mut v_b_3328_: *mut leanh::LeanObject,
    mut v_c_3329_: *mut leanh::LeanObject,
    mut v___y_3330_: *mut leanh::LeanObject,
    mut v___y_3331_: *mut leanh::LeanObject,
    mut v___y_3332_: *mut leanh::LeanObject,
    mut v___y_3333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3335_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_3324_, v_a_3327_, v_b_3328_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
    return v___x_3335_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___boxed(
    mut v_upperBound_3336_: *mut leanh::LeanObject,
    mut v_inst_3337_: *mut leanh::LeanObject,
    mut v_R_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
    mut v_b_3340_: *mut leanh::LeanObject,
    mut v_c_3341_: *mut leanh::LeanObject,
    mut v___y_3342_: *mut leanh::LeanObject,
    mut v___y_3343_: *mut leanh::LeanObject,
    mut v___y_3344_: *mut leanh::LeanObject,
    mut v___y_3345_: *mut leanh::LeanObject,
    mut v___y_3346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3347_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(
            v_upperBound_3336_,
            v_inst_3337_,
            v_R_3338_,
            v_a_3339_,
            v_b_3340_,
            v_c_3341_,
            v___y_3342_,
            v___y_3343_,
            v___y_3344_,
            v___y_3345_,
        );
    leanh::lean_dec(v___y_3345_);
    leanh::lean_dec_ref(v___y_3344_);
    leanh::lean_dec(v___y_3343_);
    leanh::lean_dec_ref(v___y_3342_);
    leanh::lean_dec(v_upperBound_3336_);
    return v_res_3347_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(
    mut v_H_3348_: *mut leanh::LeanObject,
    mut v_a_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u8 = 0;
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_unused_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v_val_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v_name_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uniq_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v_idents_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: u8 = 0;
    let mut v___x_3412_: u8 = 0;
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v_unused_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v_fst_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3439_: u8 = 0;
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3351_ = leanh::lean_ctor_get(v_a_3349_, 0);
                v_snd_3352_ = leanh::lean_ctor_get(v_a_3349_, 1);
                v___x_3353_ = lean_array_get_size(v_snd_3352_);
                v___x_3354_ = leanh::lean_unsigned_to_nat(0);
                v___x_3355_ = lean_nat_dec_eq(v___x_3353_, v___x_3354_);
                if v___x_3355_ == 0 {
                    leanh::lean_inc_ref(v_H_3348_);
                    v___x_3356_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_H_3348_);
                    if leanh::lean_obj_tag(v___x_3356_) == 1 {
                        v_isSharedCheck_3364_ =
                            (!leanh::lean_is_exclusive(v___x_3356_)) as u8;
                        if v_isSharedCheck_3364_ == 0 {
                            v_unused_3365_ = leanh::lean_ctor_get(v___x_3356_, 0);
                            leanh::lean_dec(v_unused_3365_);
                            v___x_3358_ = v___x_3356_;
                            v_isShared_3359_ = v_isSharedCheck_3364_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_3356_);
                            v___x_3358_ = leanh::lean_box(0);
                            v_isShared_3359_ = v_isSharedCheck_3364_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3356_);
                        leanh::lean_inc_ref(v_H_3348_);
                        v___x_3366_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_H_3348_);
                        if leanh::lean_obj_tag(v___x_3366_) == 1 {
                            leanh::lean_inc(v_snd_3352_);
                            leanh::lean_inc(v_fst_3351_);
                            v_isSharedCheck_3415_ =
                                (!leanh::lean_is_exclusive(v_a_3349_)) as u8;
                            if v_isSharedCheck_3415_ == 0 {
                                v_unused_3416_ = leanh::lean_ctor_get(v_a_3349_, 1);
                                leanh::lean_dec(v_unused_3416_);
                                v_unused_3417_ = leanh::lean_ctor_get(v_a_3349_, 0);
                                leanh::lean_dec(v_unused_3417_);
                                v___x_3368_ = v_a_3349_;
                                v_isShared_3369_ = v_isSharedCheck_3415_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_3349_);
                                v___x_3368_ = leanh::lean_box(0);
                                v_isShared_3369_ = v_isSharedCheck_3415_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3366_);
                            v___x_3418_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_H_3348_);
                            if leanh::lean_obj_tag(v___x_3418_) == 1 {
                                leanh::lean_dec_ref(v_H_3348_);
                                v_val_3419_ = leanh::lean_ctor_get(v___x_3418_, 0);
                                leanh::lean_inc(v_val_3419_);
                                leanh::lean_dec_ref_known(v___x_3418_, 1);
                                v_snd_3420_ = leanh::lean_ctor_get(v_val_3419_, 1);
                                leanh::lean_inc(v_snd_3420_);
                                v_snd_3421_ = leanh::lean_ctor_get(v_snd_3420_, 1);
                                leanh::lean_inc(v_snd_3421_);
                                v_fst_3422_ = leanh::lean_ctor_get(v_val_3419_, 0);
                                leanh::lean_inc(v_fst_3422_);
                                leanh::lean_dec(v_val_3419_);
                                v_fst_3423_ = leanh::lean_ctor_get(v_snd_3420_, 0);
                                leanh::lean_inc(v_fst_3423_);
                                leanh::lean_dec(v_snd_3420_);
                                v_fst_3424_ = leanh::lean_ctor_get(v_snd_3421_, 0);
                                leanh::lean_inc(v_fst_3424_);
                                v_snd_3425_ = leanh::lean_ctor_get(v_snd_3421_, 1);
                                leanh::lean_inc(v_snd_3425_);
                                leanh::lean_dec(v_snd_3421_);
                                v___x_3426_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_snd_3425_, v_a_3349_);
                                if leanh::lean_obj_tag(v___x_3426_) == 0 {
                                    v_a_3427_ = leanh::lean_ctor_get(v___x_3426_, 0);
                                    leanh::lean_inc(v_a_3427_);
                                    leanh::lean_dec_ref_known(v___x_3426_, 1);
                                    v_fst_3428_ = leanh::lean_ctor_get(v_a_3427_, 0);
                                    leanh::lean_inc(v_fst_3428_);
                                    v_snd_3429_ = leanh::lean_ctor_get(v_a_3427_, 1);
                                    leanh::lean_inc(v_snd_3429_);
                                    leanh::lean_dec(v_a_3427_);
                                    v___x_3430_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_fst_3424_, v_snd_3429_);
                                    if leanh::lean_obj_tag(v___x_3430_) == 0 {
                                        v_a_3431_ = leanh::lean_ctor_get(v___x_3430_, 0);
                                        v_isSharedCheck_3448_ =
                                            (!leanh::lean_is_exclusive(v___x_3430_)) as u8;
                                        if v_isSharedCheck_3448_ == 0 {
                                            v___x_3433_ = v___x_3430_;
                                            v_isShared_3434_ = v_isSharedCheck_3448_;
                                            state = 11;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3431_);
                                            leanh::lean_dec(v___x_3430_);
                                            v___x_3433_ = leanh::lean_box(0);
                                            v_isShared_3434_ = v_isSharedCheck_3448_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_fst_3428_);
                                        leanh::lean_dec(v_fst_3423_);
                                        leanh::lean_dec(v_fst_3422_);
                                        return v___x_3430_;
                                    }
                                } else {
                                    leanh::lean_dec(v_fst_3424_);
                                    leanh::lean_dec(v_fst_3423_);
                                    leanh::lean_dec(v_fst_3422_);
                                    return v___x_3426_;
                                }
                            } else {
                                leanh::lean_dec(v___x_3418_);
                                v___x_3449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3449_, 0, v_H_3348_);
                                leanh::lean_ctor_set(v___x_3449_, 1, v_a_3349_);
                                v___x_3450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3450_, 0, v___x_3449_);
                                return v___x_3450_;
                            }
                        }
                    }
                } else {
                    v___x_3451_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3451_, 0, v_H_3348_);
                    leanh::lean_ctor_set(v___x_3451_, 1, v_a_3349_);
                    v___x_3452_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3452_, 0, v___x_3451_);
                    return v___x_3452_;
                }
            }
            1 => {
                v___x_3360_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3360_, 0, v_H_3348_);
                leanh::lean_ctor_set(v___x_3360_, 1, v_a_3349_);
                if v_isShared_3359_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3358_, 0);
                    leanh::lean_ctor_set(v___x_3358_, 0, v___x_3360_);
                    v___x_3362_ = v___x_3358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
                    v___x_3362_ = v_reuseFailAlloc_3363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3362_;
            }
            3 => {
                v_val_3370_ = leanh::lean_ctor_get(v___x_3366_, 0);
                v_isSharedCheck_3414_ = (!leanh::lean_is_exclusive(v___x_3366_)) as u8;
                if v_isSharedCheck_3414_ == 0 {
                    v___x_3372_ = v___x_3366_;
                    v_isShared_3373_ = v_isSharedCheck_3414_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3370_);
                    leanh::lean_dec(v___x_3366_);
                    v___x_3372_ = leanh::lean_box(0);
                    v_isShared_3373_ = v_isSharedCheck_3414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_name_3374_ = leanh::lean_ctor_get(v_val_3370_, 0);
                v_uniq_3375_ = leanh::lean_ctor_get(v_val_3370_, 1);
                v_p_3376_ = leanh::lean_ctor_get(v_val_3370_, 2);
                v_isSharedCheck_3413_ = (!leanh::lean_is_exclusive(v_val_3370_)) as u8;
                if v_isSharedCheck_3413_ == 0 {
                    v___x_3378_ = v_val_3370_;
                    v_isShared_3379_ = v_isSharedCheck_3413_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_p_3376_);
                    leanh::lean_inc(v_uniq_3375_);
                    leanh::lean_inc(v_name_3374_);
                    leanh::lean_dec(v_val_3370_);
                    v___x_3378_ = leanh::lean_box(0);
                    v_isShared_3379_ = v_isSharedCheck_3413_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3411_ = l_Lean_Name_hasMacroScopes(v_name_3374_);
                if v___x_3411_ == 0 {
                    v___x_3412_ = l_Lean_NameSet_contains(v_fst_3351_, v_name_3374_);
                    if v___x_3412_ == 0 {
                        leanh::lean_del_object(v___x_3378_);
                        leanh::lean_dec_ref(v_p_3376_);
                        leanh::lean_dec(v_uniq_3375_);
                        v_idents_3381_ = v_snd_3352_;
                        state = 6;
                        continue;
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            6 => {
                v___x_3382_ = l_Lean_NameSet_insert(v_fst_3351_, v_name_3374_);
                if v_isShared_3369_ == 0 {
                    leanh::lean_ctor_set(v___x_3368_, 1, v_idents_3381_);
                    leanh::lean_ctor_set(v___x_3368_, 0, v___x_3382_);
                    v___x_3384_ = v___x_3368_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3382_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_idents_3381_);
                    v___x_3384_ = v_reuseFailAlloc_3389_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3385_, 0, v_H_3348_);
                leanh::lean_ctor_set(v___x_3385_, 1, v___x_3384_);
                if v_isShared_3373_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3372_, 0);
                    leanh::lean_ctor_set(v___x_3372_, 0, v___x_3385_);
                    v___x_3387_ = v___x_3372_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3387_;
            }
            9 => {
                v___x_3391_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2;
                v___x_3392_ = leanh::lean_box(0);
                v___x_3393_ = leanh::lean_unsigned_to_nat(1);
                v___x_3394_ = lean_nat_sub(v___x_3353_, v___x_3393_);
                v___x_3395_ = lean_array_get_borrowed(v___x_3392_, v_snd_3352_, v___x_3394_);
                leanh::lean_dec(v___x_3394_);
                leanh::lean_inc(v___x_3395_);
                v___x_3396_ = l_Lean_Syntax_isOfKind(v___x_3395_, v___x_3391_);
                if v___x_3396_ == 0 {
                    leanh::lean_del_object(v___x_3378_);
                    leanh::lean_dec_ref(v_p_3376_);
                    leanh::lean_dec(v_uniq_3375_);
                    v___x_3397_ = lean_array_pop(v_snd_3352_);
                    v_idents_3381_ = v___x_3397_;
                    state = 6;
                    continue;
                } else {
                    v___x_3398_ = l_Lean_Syntax_getArg(v___x_3395_, v___x_3354_);
                    v___x_3399_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6;
                    leanh::lean_inc(v___x_3398_);
                    v___x_3400_ = l_Lean_Syntax_isOfKind(v___x_3398_, v___x_3399_);
                    if v___x_3400_ == 0 {
                        leanh::lean_dec(v___x_3398_);
                        leanh::lean_del_object(v___x_3378_);
                        leanh::lean_dec_ref(v_p_3376_);
                        leanh::lean_dec(v_uniq_3375_);
                        v___x_3401_ = lean_array_pop(v_snd_3352_);
                        v_idents_3381_ = v___x_3401_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_name_3374_);
                        leanh::lean_del_object(v___x_3372_);
                        leanh::lean_del_object(v___x_3368_);
                        leanh::lean_dec_ref(v_H_3348_);
                        v___x_3402_ = l_Lean_TSyntax_getId(v___x_3398_);
                        leanh::lean_dec(v___x_3398_);
                        if v_isShared_3379_ == 0 {
                            leanh::lean_ctor_set(v___x_3378_, 0, v___x_3402_);
                            v___x_3404_ = v___x_3378_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3410_ =
                                leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3402_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_uniq_3375_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_p_3376_);
                            v___x_3404_ = v_reuseFailAlloc_3410_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            10 => {
                v___x_3405_ = lean_array_pop(v_snd_3352_);
                v___x_3406_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3406_, 0, v_fst_3351_);
                leanh::lean_ctor_set(v___x_3406_, 1, v___x_3405_);
                v___x_3407_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_3404_);
                v___x_3408_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3408_, 0, v___x_3407_);
                leanh::lean_ctor_set(v___x_3408_, 1, v___x_3406_);
                v___x_3409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3409_, 0, v___x_3408_);
                return v___x_3409_;
            }
            11 => {
                v_fst_3435_ = leanh::lean_ctor_get(v_a_3431_, 0);
                v_snd_3436_ = leanh::lean_ctor_get(v_a_3431_, 1);
                v_isSharedCheck_3447_ = (!leanh::lean_is_exclusive(v_a_3431_)) as u8;
                if v_isSharedCheck_3447_ == 0 {
                    v___x_3438_ = v_a_3431_;
                    v_isShared_3439_ = v_isSharedCheck_3447_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3436_);
                    leanh::lean_inc(v_fst_3435_);
                    leanh::lean_dec(v_a_3431_);
                    v___x_3438_ = leanh::lean_box(0);
                    v_isShared_3439_ = v_isSharedCheck_3447_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3440_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_fst_3422_,
                    v_fst_3423_,
                    v_fst_3435_,
                    v_fst_3428_,
                );
                if v_isShared_3439_ == 0 {
                    leanh::lean_ctor_set(v___x_3438_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3438_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_snd_3436_);
                    v___x_3442_ = v_reuseFailAlloc_3446_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3434_ == 0 {
                    leanh::lean_ctor_set(v___x_3433_, 0, v___x_3442_);
                    v___x_3444_ = v___x_3433_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg___boxed(
    mut v_H_3453_: *mut leanh::LeanObject,
    mut v_a_3454_: *mut leanh::LeanObject,
    mut v_a_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3456_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_3453_, v_a_3454_);
    return v_res_3456_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(
    mut v_H_3457_: *mut leanh::LeanObject,
    mut v_a_3458_: *mut leanh::LeanObject,
    mut v_a_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
    mut v_a_3462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3464_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_3457_, v_a_3458_);
    return v___x_3464_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___boxed(
    mut v_H_3465_: *mut leanh::LeanObject,
    mut v_a_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
    mut v_a_3468_: *mut leanh::LeanObject,
    mut v_a_3469_: *mut leanh::LeanObject,
    mut v_a_3470_: *mut leanh::LeanObject,
    mut v_a_3471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3472_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(v_H_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
    leanh::lean_dec(v_a_3470_);
    leanh::lean_dec_ref(v_a_3469_);
    leanh::lean_dec(v_a_3468_);
    leanh::lean_dec_ref(v_a_3467_);
    return v_res_3472_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(
    mut v_a_3473_: *mut leanh::LeanObject,
    mut v_a_3474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3473_) == 0 {
                    v___x_3475_ = l_List_reverse___redArg(v_a_3474_);
                    return v___x_3475_;
                } else {
                    v_head_3476_ = leanh::lean_ctor_get(v_a_3473_, 0);
                    v_tail_3477_ = leanh::lean_ctor_get(v_a_3473_, 1);
                    v_isSharedCheck_3486_ = (!leanh::lean_is_exclusive(v_a_3473_)) as u8;
                    if v_isSharedCheck_3486_ == 0 {
                        v___x_3479_ = v_a_3473_;
                        v_isShared_3480_ = v_isSharedCheck_3486_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3477_);
                        leanh::lean_inc(v_head_3476_);
                        leanh::lean_dec(v_a_3473_);
                        v___x_3479_ = leanh::lean_box(0);
                        v_isShared_3480_ = v_isSharedCheck_3486_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3481_ = l_Lean_MessageData_ofSyntax(v_head_3476_);
                if v_isShared_3480_ == 0 {
                    leanh::lean_ctor_set(v___x_3479_, 1, v_a_3474_);
                    leanh::lean_ctor_set(v___x_3479_, 0, v___x_3481_);
                    v___x_3483_ = v___x_3479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_a_3474_);
                    v___x_3483_ = v_reuseFailAlloc_3485_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3473_ = v_tail_3477_;
                v_a_3474_ = v___x_3483_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3488_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0;
    v___x_3489_ = l_Lean_stringToMessageData(v___x_3488_);
    return v___x_3489_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3491_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2;
    v___x_3492_ = l_Lean_stringToMessageData(v___x_3491_);
    return v___x_3492_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(
    mut v_goal_3493_: *mut leanh::LeanObject,
    mut v_idents_3494_: *mut leanh::LeanObject,
    mut v_a_3495_: *mut leanh::LeanObject,
    mut v_a_3496_: *mut leanh::LeanObject,
    mut v_a_3497_: *mut leanh::LeanObject,
    mut v_a_3498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v_fst_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_reuseFailAlloc_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut v_unused_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3554_: u8 = 0;
    let mut v_isSharedCheck_3555_: u8 = 0;
    let mut v_a_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_3500_ = leanh::lean_ctor_get(v_goal_3493_, 0);
                v_00_u03c3s_3501_ = leanh::lean_ctor_get(v_goal_3493_, 1);
                v_hyps_3502_ = leanh::lean_ctor_get(v_goal_3493_, 2);
                v_target_3503_ = leanh::lean_ctor_get(v_goal_3493_, 3);
                v___x_3504_ = l_Lean_NameSet_empty;
                v___x_3505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3505_, 0, v___x_3504_);
                leanh::lean_ctor_set(v___x_3505_, 1, v_idents_3494_);
                leanh::lean_inc_ref(v_hyps_3502_);
                v___x_3506_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_hyps_3502_, v___x_3505_);
                if leanh::lean_obj_tag(v___x_3506_) == 0 {
                    v_a_3507_ = leanh::lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3555_ = (!leanh::lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3555_ == 0 {
                        v___x_3509_ = v___x_3506_;
                        v_isShared_3510_ = v_isSharedCheck_3555_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3507_);
                        leanh::lean_dec(v___x_3506_);
                        v___x_3509_ = leanh::lean_box(0);
                        v_isShared_3510_ = v_isSharedCheck_3555_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_goal_3493_);
                    v_a_3556_ = leanh::lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3563_ = (!leanh::lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3563_ == 0 {
                        v___x_3558_ = v___x_3506_;
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3556_);
                        leanh::lean_dec(v___x_3506_);
                        v___x_3558_ = leanh::lean_box(0);
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3511_ = leanh::lean_ctor_get(v_a_3507_, 0);
                v_snd_3512_ = leanh::lean_ctor_get(v_a_3507_, 1);
                v_isSharedCheck_3554_ = (!leanh::lean_is_exclusive(v_a_3507_)) as u8;
                if v_isSharedCheck_3554_ == 0 {
                    v___x_3514_ = v_a_3507_;
                    v_isShared_3515_ = v_isSharedCheck_3554_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3512_);
                    leanh::lean_inc(v_fst_3511_);
                    leanh::lean_dec(v_a_3507_);
                    v___x_3514_ = leanh::lean_box(0);
                    v_isShared_3515_ = v_isSharedCheck_3554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_3521_ = leanh::lean_ctor_get(v_snd_3512_, 1);
                v_isSharedCheck_3552_ = (!leanh::lean_is_exclusive(v_snd_3512_)) as u8;
                if v_isSharedCheck_3552_ == 0 {
                    v_unused_3553_ = leanh::lean_ctor_get(v_snd_3512_, 0);
                    leanh::lean_dec(v_unused_3553_);
                    v___x_3523_ = v_snd_3512_;
                    v_isShared_3524_ = v_isSharedCheck_3552_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3521_);
                    leanh::lean_dec(v_snd_3512_);
                    v___x_3523_ = leanh::lean_box(0);
                    v_isShared_3524_ = v_isSharedCheck_3552_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_3517_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3517_, 0, v_u_3500_);
                leanh::lean_ctor_set(v___x_3517_, 1, v_00_u03c3s_3501_);
                leanh::lean_ctor_set(v___x_3517_, 2, v_fst_3511_);
                leanh::lean_ctor_set(v___x_3517_, 3, v_target_3503_);
                if v_isShared_3510_ == 0 {
                    leanh::lean_ctor_set(v___x_3509_, 0, v___x_3517_);
                    v___x_3519_ = v___x_3509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
                    v___x_3519_ = v_reuseFailAlloc_3520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3519_;
            }
            5 => {
                v___x_3525_ = lean_array_get_size(v_snd_3521_);
                v___x_3526_ = leanh::lean_unsigned_to_nat(0);
                v___x_3527_ = lean_nat_dec_eq(v___x_3525_, v___x_3526_);
                if v___x_3527_ == 0 {
                    leanh::lean_dec(v_fst_3511_);
                    leanh::lean_del_object(v___x_3509_);
                    v___x_3528_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1);
                    v___x_3529_ = lean_array_to_list(v_snd_3521_);
                    v___x_3530_ = leanh::lean_box(0);
                    v___x_3531_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(v___x_3529_, v___x_3530_);
                    v___x_3532_ = l_Lean_MessageData_ofList(v___x_3531_);
                    if v_isShared_3524_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3523_, 7);
                        leanh::lean_ctor_set(v___x_3523_, 1, v___x_3532_);
                        leanh::lean_ctor_set(v___x_3523_, 0, v___x_3528_);
                        v___x_3534_ = v___x_3523_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3551_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3528_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3532_);
                        v___x_3534_ = v_reuseFailAlloc_3551_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_target_3503_);
                    leanh::lean_inc_ref(v_00_u03c3s_3501_);
                    leanh::lean_inc(v_u_3500_);
                    leanh::lean_del_object(v___x_3523_);
                    leanh::lean_dec(v_snd_3521_);
                    leanh::lean_del_object(v___x_3514_);
                    leanh::lean_dec_ref(v_goal_3493_);
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_3535_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3);
                if v_isShared_3515_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3514_, 7);
                    leanh::lean_ctor_set(v___x_3514_, 1, v___x_3535_);
                    leanh::lean_ctor_set(v___x_3514_, 0, v___x_3534_);
                    v___x_3537_ = v___x_3514_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 1, v___x_3535_);
                    v___x_3537_ = v_reuseFailAlloc_3550_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3538_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_3493_);
                v___x_3539_ = l_Lean_MessageData_ofExpr(v___x_3538_);
                v___x_3540_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3540_, 0, v___x_3537_);
                leanh::lean_ctor_set(v___x_3540_, 1, v___x_3539_);
                v___x_3541_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_3540_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
                v_a_3542_ = leanh::lean_ctor_get(v___x_3541_, 0);
                v_isSharedCheck_3549_ = (!leanh::lean_is_exclusive(v___x_3541_)) as u8;
                if v_isSharedCheck_3549_ == 0 {
                    v___x_3544_ = v___x_3541_;
                    v_isShared_3545_ = v_isSharedCheck_3549_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3542_);
                    leanh::lean_dec(v___x_3541_);
                    v___x_3544_ = leanh::lean_box(0);
                    v_isShared_3545_ = v_isSharedCheck_3549_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3545_ == 0 {
                    v___x_3547_ = v___x_3544_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3548_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
                    v___x_3547_ = v_reuseFailAlloc_3548_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3547_;
            }
            10 => {
                if v_isShared_3559_ == 0 {
                    v___x_3561_ = v___x_3558_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
                    v___x_3561_ = v_reuseFailAlloc_3562_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___boxed(
    mut v_goal_3564_: *mut leanh::LeanObject,
    mut v_idents_3565_: *mut leanh::LeanObject,
    mut v_a_3566_: *mut leanh::LeanObject,
    mut v_a_3567_: *mut leanh::LeanObject,
    mut v_a_3568_: *mut leanh::LeanObject,
    mut v_a_3569_: *mut leanh::LeanObject,
    mut v_a_3570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3571_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(
        v_goal_3564_,
        v_idents_3565_,
        v_a_3566_,
        v_a_3567_,
        v_a_3568_,
        v_a_3569_,
    );
    leanh::lean_dec(v_a_3569_);
    leanh::lean_dec_ref(v_a_3568_);
    leanh::lean_dec(v_a_3567_);
    leanh::lean_dec_ref(v_a_3566_);
    return v_res_3571_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(
    mut v_stx_3572_: *mut leanh::LeanObject,
    mut v_lctx_3573_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_3574_: *mut leanh::LeanObject,
    mut v_expr_3575_: *mut leanh::LeanObject,
    mut v_isBinder_3576_: u8,
    mut v_x_3577_: *mut leanh::LeanObject,
    mut v___y_3578_: *mut leanh::LeanObject,
    mut v___y_3579_: *mut leanh::LeanObject,
    mut v___y_3580_: *mut leanh::LeanObject,
    mut v___y_3581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3583_ = leanh::lean_box(0);
    v___x_3584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3584_, 0, v___x_3583_);
    leanh::lean_ctor_set(v___x_3584_, 1, v_stx_3572_);
    v___x_3585_ = 0;
    v___x_3586_ = leanh::lean_alloc_ctor(0, 4, (2) as u32);
    leanh::lean_ctor_set(v___x_3586_, 0, v___x_3584_);
    leanh::lean_ctor_set(v___x_3586_, 1, v_lctx_3573_);
    leanh::lean_ctor_set(v___x_3586_, 2, v_expectedType_x3f_3574_);
    leanh::lean_ctor_set(v___x_3586_, 3, v_expr_3575_);
    leanh::lean_ctor_set_uint8(
        v___x_3586_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
        v_isBinder_3576_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3586_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 1) as u32,
        v___x_3585_,
    );
    v___x_3587_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3587_, 0, v___x_3586_);
    v___x_3588_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3588_, 0, v___x_3587_);
    v___x_3589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3589_, 0, v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed(
    mut v_stx_3590_: *mut leanh::LeanObject,
    mut v_lctx_3591_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_3592_: *mut leanh::LeanObject,
    mut v_expr_3593_: *mut leanh::LeanObject,
    mut v_isBinder_3594_: *mut leanh::LeanObject,
    mut v_x_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
    mut v___y_3597_: *mut leanh::LeanObject,
    mut v___y_3598_: *mut leanh::LeanObject,
    mut v___y_3599_: *mut leanh::LeanObject,
    mut v___y_3600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isBinder_boxed_3601_: u8 = 0;
    let mut v_res_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isBinder_boxed_3601_ = (leanh::lean_unbox(v_isBinder_3594_) as u8);
    v_res_3602_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(
        v_stx_3590_,
        v_lctx_3591_,
        v_expectedType_x3f_3592_,
        v_expr_3593_,
        v_isBinder_boxed_3601_,
        v_x_3595_,
        v___y_3596_,
        v___y_3597_,
        v___y_3598_,
        v___y_3599_,
    );
    leanh::lean_dec(v___y_3599_);
    leanh::lean_dec_ref(v___y_3598_);
    leanh::lean_dec(v___y_3597_);
    leanh::lean_dec_ref(v___y_3596_);
    return v_res_3602_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(
    mut v___x_3603_: *mut leanh::LeanObject,
    mut v___y_3604_: *mut leanh::LeanObject,
    mut v___y_3605_: *mut leanh::LeanObject,
    mut v___y_3606_: *mut leanh::LeanObject,
    mut v___y_3607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3609_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3609_, 0, v___x_3603_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed(
    mut v___x_3610_: *mut leanh::LeanObject,
    mut v___y_3611_: *mut leanh::LeanObject,
    mut v___y_3612_: *mut leanh::LeanObject,
    mut v___y_3613_: *mut leanh::LeanObject,
    mut v___y_3614_: *mut leanh::LeanObject,
    mut v___y_3615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(
        v___x_3610_,
        v___y_3611_,
        v___y_3612_,
        v___y_3613_,
        v___y_3614_,
    );
    leanh::lean_dec(v___y_3614_);
    leanh::lean_dec_ref(v___y_3613_);
    leanh::lean_dec(v___y_3612_);
    leanh::lean_dec_ref(v___y_3611_);
    return v_res_3616_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(
    mut v___x_3617_: *mut leanh::LeanObject,
    mut v___y_3618_: *mut leanh::LeanObject,
    mut v___y_3619_: *mut leanh::LeanObject,
    mut v___y_3620_: *mut leanh::LeanObject,
    mut v___y_3621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3623_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3623_, 0, v___x_3617_);
    return v___x_3623_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed(
    mut v___x_3624_: *mut leanh::LeanObject,
    mut v___y_3625_: *mut leanh::LeanObject,
    mut v___y_3626_: *mut leanh::LeanObject,
    mut v___y_3627_: *mut leanh::LeanObject,
    mut v___y_3628_: *mut leanh::LeanObject,
    mut v___y_3629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3630_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(
        v___x_3624_,
        v___y_3625_,
        v___y_3626_,
        v___y_3627_,
        v___y_3628_,
    );
    leanh::lean_dec(v___y_3628_);
    leanh::lean_dec_ref(v___y_3627_);
    leanh::lean_dec(v___y_3626_);
    leanh::lean_dec_ref(v___y_3625_);
    return v_res_3630_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3631_ = leanh::lean_unsigned_to_nat(32);
    v___x_3632_ = lean_mk_empty_array_with_capacity(v___x_3631_);
    v___x_3633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3633_, 0, v___x_3632_);
    return v___x_3633_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3634_: usize = 0;
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3634_ = 5usize;
    v___x_3635_ = leanh::lean_unsigned_to_nat(0);
    v___x_3636_ = leanh::lean_unsigned_to_nat(32);
    v___x_3637_ = lean_mk_empty_array_with_capacity(v___x_3636_);
    v___x_3638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0);
    v___x_3639_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3639_, 0, v___x_3638_);
    leanh::lean_ctor_set(v___x_3639_, 1, v___x_3637_);
    leanh::lean_ctor_set(v___x_3639_, 2, v___x_3635_);
    leanh::lean_ctor_set(v___x_3639_, 3, v___x_3635_);
    leanh::lean_ctor_set_usize(v___x_3639_, 4, v___x_3634_);
    return v___x_3639_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(
    mut v___y_3640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v_enabled_3658_: u8 = 0;
    let mut v_assignment_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3673_: u8 = 0;
    let mut v_unused_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3642_ = lean_st_ref_get(v___y_3640_);
                v_infoState_3643_ = leanh::lean_ctor_get(v___x_3642_, 7);
                leanh::lean_inc_ref(v_infoState_3643_);
                leanh::lean_dec(v___x_3642_);
                v_trees_3644_ = leanh::lean_ctor_get(v_infoState_3643_, 2);
                leanh::lean_inc_ref(v_trees_3644_);
                leanh::lean_dec_ref(v_infoState_3643_);
                v___x_3645_ = lean_st_ref_take(v___y_3640_);
                v_infoState_3646_ = leanh::lean_ctor_get(v___x_3645_, 7);
                v_env_3647_ = leanh::lean_ctor_get(v___x_3645_, 0);
                v_nextMacroScope_3648_ = leanh::lean_ctor_get(v___x_3645_, 1);
                v_ngen_3649_ = leanh::lean_ctor_get(v___x_3645_, 2);
                v_auxDeclNGen_3650_ = leanh::lean_ctor_get(v___x_3645_, 3);
                v_traceState_3651_ = leanh::lean_ctor_get(v___x_3645_, 4);
                v_cache_3652_ = leanh::lean_ctor_get(v___x_3645_, 5);
                v_messages_3653_ = leanh::lean_ctor_get(v___x_3645_, 6);
                v_snapshotTasks_3654_ = leanh::lean_ctor_get(v___x_3645_, 8);
                v_isSharedCheck_3675_ = (!leanh::lean_is_exclusive(v___x_3645_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v___x_3656_ = v___x_3645_;
                    v_isShared_3657_ = v_isSharedCheck_3675_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3654_);
                    leanh::lean_inc(v_infoState_3646_);
                    leanh::lean_inc(v_messages_3653_);
                    leanh::lean_inc(v_cache_3652_);
                    leanh::lean_inc(v_traceState_3651_);
                    leanh::lean_inc(v_auxDeclNGen_3650_);
                    leanh::lean_inc(v_ngen_3649_);
                    leanh::lean_inc(v_nextMacroScope_3648_);
                    leanh::lean_inc(v_env_3647_);
                    leanh::lean_dec(v___x_3645_);
                    v___x_3656_ = leanh::lean_box(0);
                    v_isShared_3657_ = v_isSharedCheck_3675_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_3658_ = leanh::lean_ctor_get_uint8(
                    v_infoState_3646_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_3659_ = leanh::lean_ctor_get(v_infoState_3646_, 0);
                v_lazyAssignment_3660_ = leanh::lean_ctor_get(v_infoState_3646_, 1);
                v_isSharedCheck_3673_ = (!leanh::lean_is_exclusive(v_infoState_3646_)) as u8;
                if v_isSharedCheck_3673_ == 0 {
                    v_unused_3674_ = leanh::lean_ctor_get(v_infoState_3646_, 2);
                    leanh::lean_dec(v_unused_3674_);
                    v___x_3662_ = v_infoState_3646_;
                    v_isShared_3663_ = v_isSharedCheck_3673_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_lazyAssignment_3660_);
                    leanh::lean_inc(v_assignment_3659_);
                    leanh::lean_dec(v_infoState_3646_);
                    v___x_3662_ = leanh::lean_box(0);
                    v_isShared_3663_ = v_isSharedCheck_3673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3664_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1);
                if v_isShared_3663_ == 0 {
                    leanh::lean_ctor_set(v___x_3662_, 2, v___x_3664_);
                    v___x_3666_ = v___x_3662_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_assignment_3659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_lazyAssignment_3660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3672_, 2, v___x_3664_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3672_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_3658_,
                    );
                    v___x_3666_ = v_reuseFailAlloc_3672_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3657_ == 0 {
                    leanh::lean_ctor_set(v___x_3656_, 7, v___x_3666_);
                    v___x_3668_ = v___x_3656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3671_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_env_3647_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_nextMacroScope_3648_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_ngen_3649_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_auxDeclNGen_3650_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 4, v_traceState_3651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 5, v_cache_3652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 6, v_messages_3653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 7, v___x_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3671_, 8, v_snapshotTasks_3654_);
                    v___x_3668_ = v_reuseFailAlloc_3671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3669_ = lean_st_ref_set(v___y_3640_, v___x_3668_);
                v___x_3670_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3670_, 0, v_trees_3644_);
                return v___x_3670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___boxed(
    mut v___y_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3678_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_3676_);
    leanh::lean_dec(v___y_3676_);
    return v_res_3678_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(
    mut v_mkInfoOnError_3679_: *mut leanh::LeanObject,
    mut v___y_3680_: *mut leanh::LeanObject,
    mut v___y_3681_: *mut leanh::LeanObject,
    mut v___y_3682_: *mut leanh::LeanObject,
    mut v___y_3683_: *mut leanh::LeanObject,
    mut v___f_3684_: *mut leanh::LeanObject,
    mut v_mkInfo_3685_: *mut leanh::LeanObject,
    mut v_a_x3f_3686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut v_val_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3707_: u8 = 0;
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_x3f_3686_) == 0 {
                    leanh::lean_dec_ref(v_mkInfo_3685_);
                    leanh::lean_inc(v___y_3683_);
                    leanh::lean_inc_ref(v___y_3682_);
                    leanh::lean_inc(v___y_3681_);
                    leanh::lean_inc_ref(v___y_3680_);
                    v___x_3688_ = leanh::lean_apply_5(
                        v_mkInfoOnError_3679_,
                        v___y_3680_,
                        v___y_3681_,
                        v___y_3682_,
                        v___y_3683_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3688_) == 0 {
                        v_a_3689_ = leanh::lean_ctor_get(v___x_3688_, 0);
                        leanh::lean_inc(v_a_3689_);
                        leanh::lean_dec_ref_known(v___x_3688_, 1);
                        v___x_3690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3690_, 0, v_a_3689_);
                        leanh::lean_inc(v___y_3683_);
                        leanh::lean_inc_ref(v___y_3682_);
                        leanh::lean_inc(v___y_3681_);
                        leanh::lean_inc_ref(v___y_3680_);
                        v___x_3691_ = leanh::lean_apply_6(
                            v___f_3684_,
                            v___x_3690_,
                            v___y_3680_,
                            v___y_3681_,
                            v___y_3682_,
                            v___y_3683_,
                            leanh::lean_box(0),
                        );
                        return v___x_3691_;
                    } else {
                        leanh::lean_dec_ref(v___f_3684_);
                        v_a_3692_ = leanh::lean_ctor_get(v___x_3688_, 0);
                        v_isSharedCheck_3699_ =
                            (!leanh::lean_is_exclusive(v___x_3688_)) as u8;
                        if v_isSharedCheck_3699_ == 0 {
                            v___x_3694_ = v___x_3688_;
                            v_isShared_3695_ = v_isSharedCheck_3699_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3692_);
                            leanh::lean_dec(v___x_3688_);
                            v___x_3694_ = leanh::lean_box(0);
                            v_isShared_3695_ = v_isSharedCheck_3699_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_mkInfoOnError_3679_);
                    v_val_3700_ = leanh::lean_ctor_get(v_a_x3f_3686_, 0);
                    leanh::lean_inc(v_val_3700_);
                    leanh::lean_dec_ref_known(v_a_x3f_3686_, 1);
                    leanh::lean_inc(v___y_3683_);
                    leanh::lean_inc_ref(v___y_3682_);
                    leanh::lean_inc(v___y_3681_);
                    leanh::lean_inc_ref(v___y_3680_);
                    v___x_3701_ = leanh::lean_apply_6(
                        v_mkInfo_3685_,
                        v_val_3700_,
                        v___y_3680_,
                        v___y_3681_,
                        v___y_3682_,
                        v___y_3683_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_3701_) == 0 {
                        v_a_3702_ = leanh::lean_ctor_get(v___x_3701_, 0);
                        leanh::lean_inc(v_a_3702_);
                        leanh::lean_dec_ref_known(v___x_3701_, 1);
                        leanh::lean_inc(v___y_3683_);
                        leanh::lean_inc_ref(v___y_3682_);
                        leanh::lean_inc(v___y_3681_);
                        leanh::lean_inc_ref(v___y_3680_);
                        v___x_3703_ = leanh::lean_apply_6(
                            v___f_3684_,
                            v_a_3702_,
                            v___y_3680_,
                            v___y_3681_,
                            v___y_3682_,
                            v___y_3683_,
                            leanh::lean_box(0),
                        );
                        return v___x_3703_;
                    } else {
                        leanh::lean_dec_ref(v___f_3684_);
                        v_a_3704_ = leanh::lean_ctor_get(v___x_3701_, 0);
                        v_isSharedCheck_3711_ =
                            (!leanh::lean_is_exclusive(v___x_3701_)) as u8;
                        if v_isSharedCheck_3711_ == 0 {
                            v___x_3706_ = v___x_3701_;
                            v_isShared_3707_ = v_isSharedCheck_3711_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3704_);
                            leanh::lean_dec(v___x_3701_);
                            v___x_3706_ = leanh::lean_box(0);
                            v_isShared_3707_ = v_isSharedCheck_3711_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3695_ == 0 {
                    v___x_3697_ = v___x_3694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3698_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
                    v___x_3697_ = v_reuseFailAlloc_3698_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3697_;
            }
            3 => {
                if v_isShared_3707_ == 0 {
                    v___x_3709_ = v___x_3706_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
                    v___x_3709_ = v_reuseFailAlloc_3710_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1___boxed(
    mut v_mkInfoOnError_3712_: *mut leanh::LeanObject,
    mut v___y_3713_: *mut leanh::LeanObject,
    mut v___y_3714_: *mut leanh::LeanObject,
    mut v___y_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___f_3717_: *mut leanh::LeanObject,
    mut v_mkInfo_3718_: *mut leanh::LeanObject,
    mut v_a_x3f_3719_: *mut leanh::LeanObject,
    mut v___y_3720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3721_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___f_3717_, v_mkInfo_3718_, v_a_x3f_3719_);
    leanh::lean_dec(v___y_3716_);
    leanh::lean_dec_ref(v___y_3715_);
    leanh::lean_dec(v___y_3714_);
    leanh::lean_dec_ref(v___y_3713_);
    return v_res_3721_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(
    mut v_a_3722_: *mut leanh::LeanObject,
    mut v_info_3723_: *mut leanh::LeanObject,
    mut v___y_3724_: *mut leanh::LeanObject,
    mut v___y_3725_: *mut leanh::LeanObject,
    mut v___y_3726_: *mut leanh::LeanObject,
    mut v___y_3727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___y_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_3750_: u8 = 0;
    let mut v_assignment_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v_val_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3763_: u8 = 0;
    let mut v_enabled_3764_: u8 = 0;
    let mut v_assignment_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v_val_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v_unused_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3729_ = lean_st_ref_take(v___y_3727_);
                v_env_3730_ = leanh::lean_ctor_get(v___x_3729_, 0);
                v_nextMacroScope_3731_ = leanh::lean_ctor_get(v___x_3729_, 1);
                v_ngen_3732_ = leanh::lean_ctor_get(v___x_3729_, 2);
                v_auxDeclNGen_3733_ = leanh::lean_ctor_get(v___x_3729_, 3);
                v_traceState_3734_ = leanh::lean_ctor_get(v___x_3729_, 4);
                v_cache_3735_ = leanh::lean_ctor_get(v___x_3729_, 5);
                v_messages_3736_ = leanh::lean_ctor_get(v___x_3729_, 6);
                v_infoState_3737_ = leanh::lean_ctor_get(v___x_3729_, 7);
                v_snapshotTasks_3738_ = leanh::lean_ctor_get(v___x_3729_, 8);
                v_isSharedCheck_3784_ = (!leanh::lean_is_exclusive(v___x_3729_)) as u8;
                if v_isSharedCheck_3784_ == 0 {
                    v___x_3740_ = v___x_3729_;
                    v_isShared_3741_ = v_isSharedCheck_3784_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_3738_);
                    leanh::lean_inc(v_infoState_3737_);
                    leanh::lean_inc(v_messages_3736_);
                    leanh::lean_inc(v_cache_3735_);
                    leanh::lean_inc(v_traceState_3734_);
                    leanh::lean_inc(v_auxDeclNGen_3733_);
                    leanh::lean_inc(v_ngen_3732_);
                    leanh::lean_inc(v_nextMacroScope_3731_);
                    leanh::lean_inc(v_env_3730_);
                    leanh::lean_dec(v___x_3729_);
                    v___x_3740_ = leanh::lean_box(0);
                    v_isShared_3741_ = v_isSharedCheck_3784_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_info_3723_) == 0 {
                    v_enabled_3750_ = leanh::lean_ctor_get_uint8(
                        v_infoState_3737_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_assignment_3751_ = leanh::lean_ctor_get(v_infoState_3737_, 0);
                    v_lazyAssignment_3752_ = leanh::lean_ctor_get(v_infoState_3737_, 1);
                    v_trees_3753_ = leanh::lean_ctor_get(v_infoState_3737_, 2);
                    v_isSharedCheck_3763_ =
                        (!leanh::lean_is_exclusive(v_infoState_3737_)) as u8;
                    if v_isSharedCheck_3763_ == 0 {
                        v___x_3755_ = v_infoState_3737_;
                        v_isShared_3756_ = v_isSharedCheck_3763_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_trees_3753_);
                        leanh::lean_inc(v_lazyAssignment_3752_);
                        leanh::lean_inc(v_assignment_3751_);
                        leanh::lean_dec(v_infoState_3737_);
                        v___x_3755_ = leanh::lean_box(0);
                        v_isShared_3756_ = v_isSharedCheck_3763_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_enabled_3764_ = leanh::lean_ctor_get_uint8(
                        v_infoState_3737_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_assignment_3765_ = leanh::lean_ctor_get(v_infoState_3737_, 0);
                    v_lazyAssignment_3766_ = leanh::lean_ctor_get(v_infoState_3737_, 1);
                    v_isSharedCheck_3782_ =
                        (!leanh::lean_is_exclusive(v_infoState_3737_)) as u8;
                    if v_isSharedCheck_3782_ == 0 {
                        v_unused_3783_ = leanh::lean_ctor_get(v_infoState_3737_, 2);
                        leanh::lean_dec(v_unused_3783_);
                        v___x_3768_ = v_infoState_3737_;
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_lazyAssignment_3766_);
                        leanh::lean_inc(v_assignment_3765_);
                        leanh::lean_dec(v_infoState_3737_);
                        v___x_3768_ = leanh::lean_box(0);
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3741_ == 0 {
                    leanh::lean_ctor_set(v___x_3740_, 7, v___y_3743_);
                    v___x_3745_ = v___x_3740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3749_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_env_3730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_nextMacroScope_3731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_ngen_3732_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 3, v_auxDeclNGen_3733_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 4, v_traceState_3734_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 5, v_cache_3735_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 6, v_messages_3736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 7, v___y_3743_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3749_, 8, v_snapshotTasks_3738_);
                    v___x_3745_ = v_reuseFailAlloc_3749_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3746_ = lean_st_ref_set(v___y_3727_, v___x_3745_);
                v___x_3747_ = leanh::lean_box(0);
                v___x_3748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3748_, 0, v___x_3747_);
                return v___x_3748_;
            }
            4 => {
                v_val_3757_ = leanh::lean_ctor_get(v_info_3723_, 0);
                leanh::lean_inc(v_val_3757_);
                leanh::lean_dec_ref_known(v_info_3723_, 1);
                v___x_3758_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3758_, 0, v_val_3757_);
                leanh::lean_ctor_set(v___x_3758_, 1, v_trees_3753_);
                v___x_3759_ = l_Lean_PersistentArray_push___redArg(v_a_3722_, v___x_3758_);
                if v_isShared_3756_ == 0 {
                    leanh::lean_ctor_set(v___x_3755_, 2, v___x_3759_);
                    v___x_3761_ = v___x_3755_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3762_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_assignment_3751_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_lazyAssignment_3752_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3762_, 2, v___x_3759_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3762_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_3750_,
                    );
                    v___x_3761_ = v_reuseFailAlloc_3762_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_3743_ = v___x_3761_;
                state = 2;
                continue;
            }
            6 => {
                v_val_3770_ = leanh::lean_ctor_get(v_info_3723_, 0);
                v_isSharedCheck_3781_ = (!leanh::lean_is_exclusive(v_info_3723_)) as u8;
                if v_isSharedCheck_3781_ == 0 {
                    v___x_3772_ = v_info_3723_;
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3770_);
                    leanh::lean_dec(v_info_3723_);
                    v___x_3772_ = leanh::lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3773_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3772_, 2);
                    v___x_3775_ = v___x_3772_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_val_3770_);
                    v___x_3775_ = v_reuseFailAlloc_3780_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3776_ = l_Lean_PersistentArray_push___redArg(v_a_3722_, v___x_3775_);
                if v_isShared_3769_ == 0 {
                    leanh::lean_ctor_set(v___x_3768_, 2, v___x_3776_);
                    v___x_3778_ = v___x_3768_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3779_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_assignment_3765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_lazyAssignment_3766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3779_, 2, v___x_3776_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_enabled_3764_,
                    );
                    v___x_3778_ = v_reuseFailAlloc_3779_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_3743_ = v___x_3778_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed(
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_info_3786_: *mut leanh::LeanObject,
    mut v___y_3787_: *mut leanh::LeanObject,
    mut v___y_3788_: *mut leanh::LeanObject,
    mut v___y_3789_: *mut leanh::LeanObject,
    mut v___y_3790_: *mut leanh::LeanObject,
    mut v___y_3791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(v_a_3785_, v_info_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
    leanh::lean_dec(v___y_3790_);
    leanh::lean_dec_ref(v___y_3789_);
    leanh::lean_dec(v___y_3788_);
    leanh::lean_dec_ref(v___y_3787_);
    return v_res_3792_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(
    mut v_x_3793_: *mut leanh::LeanObject,
    mut v_mkInfo_3794_: *mut leanh::LeanObject,
    mut v_mkInfoOnError_3795_: *mut leanh::LeanObject,
    mut v___y_3796_: *mut leanh::LeanObject,
    mut v___y_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
    mut v___y_3799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_3803_: u8 = 0;
    let mut v___x_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v_unused_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut v_reuseFailAlloc_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_a_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_unused_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3801_ = lean_st_ref_get(v___y_3799_);
                v_infoState_3802_ = leanh::lean_ctor_get(v___x_3801_, 7);
                leanh::lean_inc_ref(v_infoState_3802_);
                leanh::lean_dec(v___x_3801_);
                v_enabled_3803_ = leanh::lean_ctor_get_uint8(
                    v_infoState_3802_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                leanh::lean_dec_ref(v_infoState_3802_);
                if v_enabled_3803_ == 0 {
                    leanh::lean_dec_ref(v_mkInfoOnError_3795_);
                    leanh::lean_dec_ref(v_mkInfo_3794_);
                    leanh::lean_inc(v___y_3799_);
                    leanh::lean_inc_ref(v___y_3798_);
                    leanh::lean_inc(v___y_3797_);
                    leanh::lean_inc_ref(v___y_3796_);
                    v___x_3804_ = leanh::lean_apply_5(
                        v_x_3793_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        leanh::lean_box(0),
                    );
                    return v___x_3804_;
                } else {
                    v___x_3805_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_3799_);
                    v_a_3806_ = leanh::lean_ctor_get(v___x_3805_, 0);
                    leanh::lean_inc(v_a_3806_);
                    leanh::lean_dec_ref(v___x_3805_);
                    v___f_3807_ = leanh::lean_alloc_closure(l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    leanh::lean_closure_set(v___f_3807_, 0, v_a_3806_);
                    leanh::lean_inc(v___y_3799_);
                    leanh::lean_inc_ref(v___y_3798_);
                    leanh::lean_inc(v___y_3797_);
                    leanh::lean_inc_ref(v___y_3796_);
                    v_r_3808_ = leanh::lean_apply_5(
                        v_x_3793_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v_r_3808_) == 0 {
                        v_a_3809_ = leanh::lean_ctor_get(v_r_3808_, 0);
                        v_isSharedCheck_3833_ = (!leanh::lean_is_exclusive(v_r_3808_)) as u8;
                        if v_isSharedCheck_3833_ == 0 {
                            v___x_3811_ = v_r_3808_;
                            v_isShared_3812_ = v_isSharedCheck_3833_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3809_);
                            leanh::lean_dec(v_r_3808_);
                            v___x_3811_ = leanh::lean_box(0);
                            v_isShared_3812_ = v_isSharedCheck_3833_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3834_ = leanh::lean_ctor_get(v_r_3808_, 0);
                        leanh::lean_inc(v_a_3834_);
                        leanh::lean_dec_ref_known(v_r_3808_, 1);
                        v___x_3835_ = leanh::lean_box(0);
                        v___x_3836_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___f_3807_, v_mkInfo_3794_, v___x_3835_);
                        if leanh::lean_obj_tag(v___x_3836_) == 0 {
                            v_isSharedCheck_3843_ =
                                (!leanh::lean_is_exclusive(v___x_3836_)) as u8;
                            if v_isSharedCheck_3843_ == 0 {
                                v_unused_3844_ = leanh::lean_ctor_get(v___x_3836_, 0);
                                leanh::lean_dec(v_unused_3844_);
                                v___x_3838_ = v___x_3836_;
                                v_isShared_3839_ = v_isSharedCheck_3843_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3836_);
                                v___x_3838_ = leanh::lean_box(0);
                                v_isShared_3839_ = v_isSharedCheck_3843_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_3834_);
                            v_a_3845_ = leanh::lean_ctor_get(v___x_3836_, 0);
                            v_isSharedCheck_3852_ =
                                (!leanh::lean_is_exclusive(v___x_3836_)) as u8;
                            if v_isSharedCheck_3852_ == 0 {
                                v___x_3847_ = v___x_3836_;
                                v_isShared_3848_ = v_isSharedCheck_3852_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3845_);
                                leanh::lean_dec(v___x_3836_);
                                v___x_3847_ = leanh::lean_box(0);
                                v_isShared_3848_ = v_isSharedCheck_3852_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_3809_);
                if v_isShared_3812_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3811_, 1);
                    v___x_3814_ = v___x_3811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3809_);
                    v___x_3814_ = v_reuseFailAlloc_3832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3815_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___f_3807_, v_mkInfo_3794_, v___x_3814_);
                if leanh::lean_obj_tag(v___x_3815_) == 0 {
                    v_isSharedCheck_3822_ = (!leanh::lean_is_exclusive(v___x_3815_)) as u8;
                    if v_isSharedCheck_3822_ == 0 {
                        v_unused_3823_ = leanh::lean_ctor_get(v___x_3815_, 0);
                        leanh::lean_dec(v_unused_3823_);
                        v___x_3817_ = v___x_3815_;
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3815_);
                        v___x_3817_ = leanh::lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3809_);
                    v_a_3824_ = leanh::lean_ctor_get(v___x_3815_, 0);
                    v_isSharedCheck_3831_ = (!leanh::lean_is_exclusive(v___x_3815_)) as u8;
                    if v_isSharedCheck_3831_ == 0 {
                        v___x_3826_ = v___x_3815_;
                        v_isShared_3827_ = v_isSharedCheck_3831_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3824_);
                        leanh::lean_dec(v___x_3815_);
                        v___x_3826_ = leanh::lean_box(0);
                        v_isShared_3827_ = v_isSharedCheck_3831_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3818_ == 0 {
                    leanh::lean_ctor_set(v___x_3817_, 0, v_a_3809_);
                    v___x_3820_ = v___x_3817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3809_);
                    v___x_3820_ = v_reuseFailAlloc_3821_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3820_;
            }
            5 => {
                if v_isShared_3827_ == 0 {
                    v___x_3829_ = v___x_3826_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
                    v___x_3829_ = v_reuseFailAlloc_3830_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3829_;
            }
            7 => {
                if v_isShared_3839_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3838_, 1);
                    leanh::lean_ctor_set(v___x_3838_, 0, v_a_3834_);
                    v___x_3841_ = v___x_3838_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3834_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3841_;
            }
            9 => {
                if v_isShared_3848_ == 0 {
                    v___x_3850_ = v___x_3847_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
                    v___x_3850_ = v_reuseFailAlloc_3851_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___boxed(
    mut v_x_3853_: *mut leanh::LeanObject,
    mut v_mkInfo_3854_: *mut leanh::LeanObject,
    mut v_mkInfoOnError_3855_: *mut leanh::LeanObject,
    mut v___y_3856_: *mut leanh::LeanObject,
    mut v___y_3857_: *mut leanh::LeanObject,
    mut v___y_3858_: *mut leanh::LeanObject,
    mut v___y_3859_: *mut leanh::LeanObject,
    mut v___y_3860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_3853_, v_mkInfo_3854_, v_mkInfoOnError_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
    leanh::lean_dec(v___y_3859_);
    leanh::lean_dec_ref(v___y_3858_);
    leanh::lean_dec(v___y_3857_);
    leanh::lean_dec_ref(v___y_3856_);
    return v_res_3861_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
    mut v_stx_3864_: *mut leanh::LeanObject,
    mut v_lctx_3865_: *mut leanh::LeanObject,
    mut v_expr_3866_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_3867_: *mut leanh::LeanObject,
    mut v_isBinder_3868_: u8,
    mut v_a_3869_: *mut leanh::LeanObject,
    mut v_a_3870_: *mut leanh::LeanObject,
    mut v_a_3871_: *mut leanh::LeanObject,
    mut v_a_3872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3874_ = leanh::lean_box((v_isBinder_3868_) as usize);
    leanh::lean_inc(v_expectedType_x3f_3867_);
    leanh::lean_inc_ref(v_lctx_3865_);
    leanh::lean_inc(v_stx_3864_);
    v___f_3875_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed as *mut core::ffi::c_void,
        11,
        5,
    );
    leanh::lean_closure_set(v___f_3875_, 0, v_stx_3864_);
    leanh::lean_closure_set(v___f_3875_, 1, v_lctx_3865_);
    leanh::lean_closure_set(v___f_3875_, 2, v_expectedType_x3f_3867_);
    leanh::lean_closure_set(v___f_3875_, 3, v_expr_3866_);
    leanh::lean_closure_set(v___f_3875_, 4, v___x_3874_);
    v___f_3876_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0;
    v___x_3877_ = leanh::lean_box(0);
    v___x_3878_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3878_, 0, v___x_3877_);
    leanh::lean_ctor_set(v___x_3878_, 1, v_stx_3864_);
    v___x_3879_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3879_, 0, v___x_3878_);
    leanh::lean_ctor_set(v___x_3879_, 1, v_lctx_3865_);
    leanh::lean_ctor_set(v___x_3879_, 2, v_expectedType_x3f_3867_);
    v___x_3880_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3880_, 0, v___x_3879_);
    v___f_3881_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3881_, 0, v___x_3880_);
    v___x_3882_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v___f_3876_, v___f_3875_, v___f_3881_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
    return v___x_3882_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed(
    mut v_stx_3883_: *mut leanh::LeanObject,
    mut v_lctx_3884_: *mut leanh::LeanObject,
    mut v_expr_3885_: *mut leanh::LeanObject,
    mut v_expectedType_x3f_3886_: *mut leanh::LeanObject,
    mut v_isBinder_3887_: *mut leanh::LeanObject,
    mut v_a_3888_: *mut leanh::LeanObject,
    mut v_a_3889_: *mut leanh::LeanObject,
    mut v_a_3890_: *mut leanh::LeanObject,
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isBinder_boxed_3893_: u8 = 0;
    let mut v_res_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isBinder_boxed_3893_ = (leanh::lean_unbox(v_isBinder_3887_) as u8);
    v_res_3894_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
        v_stx_3883_,
        v_lctx_3884_,
        v_expr_3885_,
        v_expectedType_x3f_3886_,
        v_isBinder_boxed_3893_,
        v_a_3888_,
        v_a_3889_,
        v_a_3890_,
        v_a_3891_,
    );
    leanh::lean_dec(v_a_3891_);
    leanh::lean_dec_ref(v_a_3890_);
    leanh::lean_dec(v_a_3889_);
    leanh::lean_dec_ref(v_a_3888_);
    return v_res_3894_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(
    mut v___y_3895_: *mut leanh::LeanObject,
    mut v___y_3896_: *mut leanh::LeanObject,
    mut v___y_3897_: *mut leanh::LeanObject,
    mut v___y_3898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3900_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_3898_);
    return v___x_3900_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___boxed(
    mut v___y_3901_: *mut leanh::LeanObject,
    mut v___y_3902_: *mut leanh::LeanObject,
    mut v___y_3903_: *mut leanh::LeanObject,
    mut v___y_3904_: *mut leanh::LeanObject,
    mut v___y_3905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3906_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
    leanh::lean_dec(v___y_3904_);
    leanh::lean_dec_ref(v___y_3903_);
    leanh::lean_dec(v___y_3902_);
    leanh::lean_dec_ref(v___y_3901_);
    return v_res_3906_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(
    mut v_00_u03b1_3907_: *mut leanh::LeanObject,
    mut v_x_3908_: *mut leanh::LeanObject,
    mut v_mkInfo_3909_: *mut leanh::LeanObject,
    mut v_mkInfoOnError_3910_: *mut leanh::LeanObject,
    mut v___y_3911_: *mut leanh::LeanObject,
    mut v___y_3912_: *mut leanh::LeanObject,
    mut v___y_3913_: *mut leanh::LeanObject,
    mut v___y_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3916_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_3908_, v_mkInfo_3909_, v_mkInfoOnError_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
    return v___x_3916_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___boxed(
    mut v_00_u03b1_3917_: *mut leanh::LeanObject,
    mut v_x_3918_: *mut leanh::LeanObject,
    mut v_mkInfo_3919_: *mut leanh::LeanObject,
    mut v_mkInfoOnError_3920_: *mut leanh::LeanObject,
    mut v___y_3921_: *mut leanh::LeanObject,
    mut v___y_3922_: *mut leanh::LeanObject,
    mut v___y_3923_: *mut leanh::LeanObject,
    mut v___y_3924_: *mut leanh::LeanObject,
    mut v___y_3925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(v_00_u03b1_3917_, v_x_3918_, v_mkInfo_3919_, v_mkInfoOnError_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
    leanh::lean_dec(v___y_3924_);
    leanh::lean_dec_ref(v___y_3923_);
    leanh::lean_dec(v___y_3922_);
    leanh::lean_dec_ref(v___y_3921_);
    return v_res_3926_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
    mut v_stx_3933_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3934_: *mut leanh::LeanObject,
    mut v_hyp_3935_: *mut leanh::LeanObject,
    mut v_isBinder_3936_: u8,
    mut v_a_3937_: *mut leanh::LeanObject,
    mut v_a_3938_: *mut leanh::LeanObject,
    mut v_a_3939_: *mut leanh::LeanObject,
    mut v_a_3940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uniq_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: u8 = 0;
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3959_: u8 = 0;
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3942_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1;
                v___x_3943_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v___x_3942_,
                    v_a_3937_,
                    v_a_3938_,
                    v_a_3939_,
                    v_a_3940_,
                );
                if leanh::lean_obj_tag(v___x_3943_) == 0 {
                    v_a_3944_ = leanh::lean_ctor_get(v___x_3943_, 0);
                    leanh::lean_inc(v_a_3944_);
                    leanh::lean_dec_ref_known(v___x_3943_, 1);
                    v_lctx_3945_ = leanh::lean_ctor_get(v_a_3937_, 2);
                    v_name_3946_ = leanh::lean_ctor_get(v_hyp_3935_, 0);
                    leanh::lean_inc(v_name_3946_);
                    v_uniq_3947_ = leanh::lean_ctor_get(v_hyp_3935_, 1);
                    leanh::lean_inc_n(v_uniq_3947_, 2);
                    v_p_3948_ = leanh::lean_ctor_get(v_hyp_3935_, 2);
                    leanh::lean_inc_ref(v_p_3948_);
                    leanh::lean_dec_ref(v_hyp_3935_);
                    v___x_3949_ = l_Lean_mkAppB(v_a_3944_, v_00_u03c3s_3934_, v_p_3948_);
                    v___x_3950_ = 0;
                    v___x_3951_ = 0;
                    leanh::lean_inc_ref(v___x_3949_);
                    leanh::lean_inc_ref(v_lctx_3945_);
                    v___x_3952_ = l_Lean_LocalContext_mkLocalDecl(
                        v_lctx_3945_,
                        v_uniq_3947_,
                        v_name_3946_,
                        v___x_3949_,
                        v___x_3950_,
                        v___x_3951_,
                    );
                    v___x_3953_ = l_Lean_Expr_fvar___override(v_uniq_3947_);
                    v___x_3954_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3954_, 0, v___x_3949_);
                    v___x_3955_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
                        v_stx_3933_,
                        v___x_3952_,
                        v___x_3953_,
                        v___x_3954_,
                        v_isBinder_3936_,
                        v_a_3937_,
                        v_a_3938_,
                        v_a_3939_,
                        v_a_3940_,
                    );
                    return v___x_3955_;
                } else {
                    leanh::lean_dec_ref(v_hyp_3935_);
                    leanh::lean_dec_ref(v_00_u03c3s_3934_);
                    leanh::lean_dec(v_stx_3933_);
                    v_a_3956_ = leanh::lean_ctor_get(v___x_3943_, 0);
                    v_isSharedCheck_3963_ = (!leanh::lean_is_exclusive(v___x_3943_)) as u8;
                    if v_isSharedCheck_3963_ == 0 {
                        v___x_3958_ = v___x_3943_;
                        v_isShared_3959_ = v_isSharedCheck_3963_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3956_);
                        leanh::lean_dec(v___x_3943_);
                        v___x_3958_ = leanh::lean_box(0);
                        v_isShared_3959_ = v_isSharedCheck_3963_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3959_ == 0 {
                    v___x_3961_ = v___x_3958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
                    v___x_3961_ = v_reuseFailAlloc_3962_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___boxed(
    mut v_stx_3964_: *mut leanh::LeanObject,
    mut v_00_u03c3s_3965_: *mut leanh::LeanObject,
    mut v_hyp_3966_: *mut leanh::LeanObject,
    mut v_isBinder_3967_: *mut leanh::LeanObject,
    mut v_a_3968_: *mut leanh::LeanObject,
    mut v_a_3969_: *mut leanh::LeanObject,
    mut v_a_3970_: *mut leanh::LeanObject,
    mut v_a_3971_: *mut leanh::LeanObject,
    mut v_a_3972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isBinder_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isBinder_boxed_3973_ = (leanh::lean_unbox(v_isBinder_3967_) as u8);
    v_res_3974_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
        v_stx_3964_,
        v_00_u03c3s_3965_,
        v_hyp_3966_,
        v_isBinder_boxed_3973_,
        v_a_3968_,
        v_a_3969_,
        v_a_3970_,
        v_a_3971_,
    );
    leanh::lean_dec(v_a_3971_);
    leanh::lean_dec_ref(v_a_3970_);
    leanh::lean_dec(v_a_3969_);
    leanh::lean_dec_ref(v_a_3968_);
    return v_res_3974_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred_DerivedLaws(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_ProofMode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default);
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred_DerivedLaws(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_Do_ProofMode(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
}