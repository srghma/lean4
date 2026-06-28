// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.MGoal
// Imports: Std.Do.SPred.DerivedLaws Std.Tactic.Do.ProofMode Lean.Elab.Tactic.Basic
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::GetElem::l_List_get_x21Internal___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_pop, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0_value) as *mut LeanObject,5949480926448383572 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 110, 105, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0_value) as *mut LeanObject,540998345785676541 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value: LeanStringObject<3> =
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
        m_data: [68, 111, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0_value)
                as *mut LeanObject,
            7100147834070349651 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__0_value)
                as *mut LeanObject,
            7792321844762638861 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value)
        as *mut LeanObject;
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0_value)
                as *mut LeanObject,
            11870096045526947150 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__0_value)
                as *mut LeanObject,
            14620467112940626392 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__0_value)
                as *mut LeanObject,
            2230670361559575988 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__2_value)
                as *mut LeanObject,
            11548698969284563040 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value: LeanStringObject<10> =
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
        m_data: [98, 105, 101, 110, 116, 97, 105, 108, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__4_value)
                as *mut LeanObject,
            8550510443043304393 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__5_value)
                as *mut LeanObject,
            14477891125163417350 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
                as *mut LeanObject,
            9582258842178272501 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
                as *mut LeanObject,
            9582258842178272501 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__0_value)
                as *mut LeanObject,
            18135193680607614554 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__0_value)
                as *mut LeanObject,
            9582258842178272501 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__0_value)
                as *mut LeanObject,
            8614124190858717794 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value:
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
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__0_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value: LeanStringObject<7> =
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
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value)
                as *mut LeanObject,
            5139300886809190733 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            1041404937882640577 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__1_value)
                as *mut LeanObject,
            12835071094194112971 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0_value: LeanStringObject<18> =
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
            78, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__0_value)
                as *mut LeanObject,
            515334035361346902 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 77, 71, 111, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1_value: LeanStringObject<95> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 95, m_capacity: 95, m_length: 94, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 77, 71, 111, 97, 108, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 77, 71, 111, 97, 108, 46, 102, 105, 110, 100, 72, 121, 112, 63, 46, 103, 111, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2_value: LeanStringObject<56> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 56, m_capacity: 56, m_length: 55, m_data: [77, 71, 111, 97, 108, 46, 102, 105, 110, 100, 72, 121, 112, 63, 58, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 119, 105, 116, 104, 111, 117, 116, 32, 112, 114, 111, 112, 101, 114, 32, 109, 101, 116, 97, 100, 97, 116, 97, 58, 32, 123, 101, 125, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0_value: LeanStringObject<20> =
    LeanStringObject {
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
            115, 116, 114, 97, 121, 32, 99, 104, 101, 99, 107, 72, 97, 115, 84, 121, 112, 101, 32,
            0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4_value: LeanStringObject<96> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 96,
        m_capacity: 96,
        m_length: 95,
        m_data: [
            99, 104, 101, 99, 107, 72, 97, 115, 84, 121, 112, 101, 58, 32, 116, 104, 101, 32, 101,
            120, 112, 114, 101, 115, 115, 105, 111, 110, 39, 115, 32, 105, 110, 102, 101, 114, 114,
            101, 100, 32, 116, 121, 112, 101, 32, 97, 110, 100, 32, 105, 116, 115, 32, 101, 120,
            112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 100, 105, 100, 32, 110, 111,
            116, 32, 109, 97, 116, 99, 104, 46, 10, 10, 32, 32, 32, 32, 32, 32, 101, 120, 112, 114,
            58, 32, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            10, 10, 32, 32, 32, 32, 32, 32, 104, 97, 115, 32, 105, 110, 102, 101, 114, 114, 101,
            100, 32, 116, 121, 112, 101, 58, 32, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8_value: LeanStringObject<36> =
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
            10, 10, 32, 32, 32, 32, 32, 32, 98, 117, 116, 32, 116, 104, 101, 32, 101, 120, 112,
            101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 119, 97, 115, 58, 32, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__1_value)
                as *mut LeanObject,
            13771926289831477797 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__3_value)
                as *mut LeanObject,
            8738205681931236784 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__5_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0_value)
        as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [65, 109, 98, 105, 101, 110, 116, 32, 115, 116, 97, 116, 101, 32, 108, 105, 115, 116, 32, 110, 111, 116, 32, 97, 32, 99, 111, 110, 115, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0_value:
    LeanStringObject<55> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value: LeanStringObject<15> =
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
            77, 71, 111, 97, 108, 72, 121, 112, 77, 97, 114, 107, 101, 114, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0_value)
                as *mut LeanObject,
            5139300886809190733 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1_value)
                as *mut LeanObject,
            1041404937882640577 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__0_value)
                as *mut LeanObject,
            8141127944165067620 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(
    mut v_x_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_data_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: u8 = 0;
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2021_: u8 = 0;
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1996_) == 10 {
                    v_data_1997_ = lean_ctor_get(v_x_1996_, 0);
                    lean_inc(v_data_1997_);
                    if lean_obj_tag(v_data_1997_) == 1 {
                        v_head_1998_ = lean_ctor_get(v_data_1997_, 0);
                        lean_inc(v_head_1998_);
                        v_fst_1999_ = lean_ctor_get(v_head_1998_, 0);
                        lean_inc(v_fst_1999_);
                        if lean_obj_tag(v_fst_1999_) == 1 {
                            v_pre_2000_ = lean_ctor_get(v_fst_1999_, 0);
                            if lean_obj_tag(v_pre_2000_) == 0 {
                                v_expr_2001_ = lean_ctor_get(v_x_1996_, 1);
                                lean_inc_ref(v_expr_2001_);
                                lean_dec_ref_known(v_x_1996_, 2);
                                v_tail_2002_ = lean_ctor_get(v_data_1997_, 1);
                                lean_inc(v_tail_2002_);
                                lean_dec_ref_known(v_data_1997_, 2);
                                v_snd_2003_ = lean_ctor_get(v_head_1998_, 1);
                                lean_inc(v_snd_2003_);
                                lean_dec(v_head_1998_);
                                v_str_2004_ = lean_ctor_get(v_fst_1999_, 1);
                                lean_inc_ref(v_str_2004_);
                                lean_dec_ref_known(v_fst_1999_, 2);
                                v___x_2005_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation___closed__0;
                                v___x_2006_ = lean_string_dec_eq(v_str_2004_, v___x_2005_);
                                lean_dec_ref(v_str_2004_);
                                if v___x_2006_ == 0 {
                                    lean_dec(v_snd_2003_);
                                    lean_dec(v_tail_2002_);
                                    lean_dec_ref(v_expr_2001_);
                                    v___x_2007_ = lean_box(0);
                                    return v___x_2007_;
                                } else {
                                    if lean_obj_tag(v_snd_2003_) == 2 {
                                        if lean_obj_tag(v_tail_2002_) == 1 {
                                            v_head_2008_ = lean_ctor_get(v_tail_2002_, 0);
                                            lean_inc(v_head_2008_);
                                            v_fst_2009_ = lean_ctor_get(v_head_2008_, 0);
                                            lean_inc(v_fst_2009_);
                                            if lean_obj_tag(v_fst_2009_) == 1 {
                                                v_pre_2010_ = lean_ctor_get(v_fst_2009_, 0);
                                                if lean_obj_tag(v_pre_2010_) == 0 {
                                                    v_v_2011_ = lean_ctor_get(v_snd_2003_, 0);
                                                    lean_inc(v_v_2011_);
                                                    lean_dec_ref_known(v_snd_2003_, 1);
                                                    v_tail_2012_ = lean_ctor_get(v_tail_2002_, 1);
                                                    lean_inc(v_tail_2012_);
                                                    lean_dec_ref_known(v_tail_2002_, 2);
                                                    v_snd_2013_ = lean_ctor_get(v_head_2008_, 1);
                                                    lean_inc(v_snd_2013_);
                                                    lean_dec(v_head_2008_);
                                                    v_str_2014_ = lean_ctor_get(v_fst_2009_, 1);
                                                    lean_inc_ref(v_str_2014_);
                                                    lean_dec_ref_known(v_fst_2009_, 2);
                                                    v___x_2015_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation___closed__0;
                                                    v___x_2016_ = lean_string_dec_eq(
                                                        v_str_2014_,
                                                        v___x_2015_,
                                                    );
                                                    lean_dec_ref(v_str_2014_);
                                                    if v___x_2016_ == 0 {
                                                        lean_dec(v_snd_2013_);
                                                        lean_dec(v_tail_2012_);
                                                        lean_dec(v_v_2011_);
                                                        lean_dec_ref(v_expr_2001_);
                                                        v___x_2017_ = lean_box(0);
                                                        return v___x_2017_;
                                                    } else {
                                                        if lean_obj_tag(v_snd_2013_) == 2 {
                                                            if lean_obj_tag(v_tail_2012_) == 0 {
                                                                v_v_2018_ =
                                                                    lean_ctor_get(v_snd_2013_, 0);
                                                                v_isSharedCheck_2026_ =
                                                                    (!lean_is_exclusive(
                                                                        v_snd_2013_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2026_ == 0 {
                                                                    v___x_2020_ = v_snd_2013_;
                                                                    v_isShared_2021_ =
                                                                        v_isSharedCheck_2026_;
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_v_2018_);
                                                                    lean_dec(v_snd_2013_);
                                                                    v___x_2020_ = lean_box(0);
                                                                    v_isShared_2021_ =
                                                                        v_isSharedCheck_2026_;
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v_snd_2013_, 1);
                                                                lean_dec(v_tail_2012_);
                                                                lean_dec(v_v_2011_);
                                                                lean_dec_ref(v_expr_2001_);
                                                                v___x_2027_ = lean_box(0);
                                                                return v___x_2027_;
                                                            }
                                                        } else {
                                                            lean_dec(v_snd_2013_);
                                                            lean_dec(v_tail_2012_);
                                                            lean_dec(v_v_2011_);
                                                            lean_dec_ref(v_expr_2001_);
                                                            v___x_2028_ = lean_box(0);
                                                            return v___x_2028_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v_fst_2009_, 2);
                                                    lean_dec(v_head_2008_);
                                                    lean_dec_ref_known(v_tail_2002_, 2);
                                                    lean_dec_ref_known(v_snd_2003_, 1);
                                                    lean_dec_ref(v_expr_2001_);
                                                    v___x_2029_ = lean_box(0);
                                                    return v___x_2029_;
                                                }
                                            } else {
                                                lean_dec(v_fst_2009_);
                                                lean_dec(v_head_2008_);
                                                lean_dec_ref_known(v_tail_2002_, 2);
                                                lean_dec_ref_known(v_snd_2003_, 1);
                                                lean_dec_ref(v_expr_2001_);
                                                v___x_2030_ = lean_box(0);
                                                return v___x_2030_;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_snd_2003_, 1);
                                            lean_dec(v_tail_2002_);
                                            lean_dec_ref(v_expr_2001_);
                                            v___x_2031_ = lean_box(0);
                                            return v___x_2031_;
                                        }
                                    } else {
                                        lean_dec(v_snd_2003_);
                                        lean_dec(v_tail_2002_);
                                        lean_dec_ref(v_expr_2001_);
                                        v___x_2032_ = lean_box(0);
                                        return v___x_2032_;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v_fst_1999_, 2);
                                lean_dec_ref_known(v_data_1997_, 2);
                                lean_dec(v_head_1998_);
                                lean_dec_ref_known(v_x_1996_, 2);
                                v___x_2033_ = lean_box(0);
                                return v___x_2033_;
                            }
                        } else {
                            lean_dec(v_fst_1999_);
                            lean_dec_ref_known(v_data_1997_, 2);
                            lean_dec(v_head_1998_);
                            lean_dec_ref_known(v_x_1996_, 2);
                            v___x_2034_ = lean_box(0);
                            return v___x_2034_;
                        }
                    } else {
                        lean_dec(v_data_1997_);
                        lean_dec_ref_known(v_x_1996_, 2);
                        v___x_2035_ = lean_box(0);
                        return v___x_2035_;
                    }
                } else {
                    lean_dec_ref(v_x_1996_);
                    v___x_2036_ = lean_box(0);
                    return v___x_2036_;
                }
            }
            1 => {
                v___x_2022_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2022_, 0, v_v_2011_);
                lean_ctor_set(v___x_2022_, 1, v_v_2018_);
                lean_ctor_set(v___x_2022_, 2, v_expr_2001_);
                if v_isShared_2021_ == 0 {
                    lean_ctor_set_tag(v___x_2020_, 1);
                    lean_ctor_set(v___x_2020_, 0, v___x_2022_);
                    v___x_2024_ = v___x_2020_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
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
    mut v_hyp_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    v_name_2038_ = lean_ctor_get(v_hyp_2037_, 0);
    lean_inc(v_name_2038_);
    v_uniq_2039_ = lean_ctor_get(v_hyp_2037_, 1);
    lean_inc(v_uniq_2039_);
    v_p_2040_ = lean_ctor_get(v_hyp_2037_, 2);
    lean_inc_ref(v_p_2040_);
    lean_dec_ref(v_hyp_2037_);
    v___x_2041_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_nameAnnotation;
    v___x_2042_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2042_, 0, v_name_2038_);
    v___x_2043_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2043_, 0, v___x_2041_);
    lean_ctor_set(v___x_2043_, 1, v___x_2042_);
    v___x_2044_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_uniqAnnotation;
    v___x_2045_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_2045_, 0, v_uniq_2039_);
    v___x_2046_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2046_, 0, v___x_2044_);
    lean_ctor_set(v___x_2046_, 1, v___x_2045_);
    v___x_2047_ = lean_box(0);
    v___x_2048_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2048_, 0, v___x_2046_);
    lean_ctor_set(v___x_2048_, 1, v___x_2047_);
    v___x_2049_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2049_, 0, v___x_2043_);
    lean_ctor_set(v___x_2049_, 1, v___x_2048_);
    v___x_2050_ = l_Lean_Expr_mdata___override(v___x_2049_, v_p_2040_);
    return v___x_2050_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType(
    mut v_u_2058_: *mut LeanObject,
    mut v_00_u03c3s_2059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    v___x_2060_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__3;
    v___x_2061_ = lean_box(0);
    v___x_2062_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2062_, 0, v_u_2058_);
    lean_ctor_set(v___x_2062_, 1, v___x_2061_);
    v___x_2063_ = l_Lean_mkConst(v___x_2060_, v___x_2062_);
    v___x_2064_ = l_Lean_Expr_app___override(v___x_2063_, v_00_u03c3s_2059_);
    return v___x_2064_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(
    mut v_u_2071_: *mut LeanObject,
    mut v_00_u03c3s_2072_: *mut LeanObject,
    mut v_p_2073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__1;
    v___x_2075_ = lean_box(0);
    v___x_2076_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2076_, 0, v_u_2071_);
    lean_ctor_set(v___x_2076_, 1, v___x_2075_);
    v___x_2077_ = l_Lean_mkConst(v___x_2074_, v___x_2076_);
    v___x_2078_ = l_Lean_mkAppB(v___x_2077_, v_00_u03c3s_2072_, v_p_2073_);
    return v___x_2078_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(
    mut v_x_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: u8 = 0;
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_unused_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2079_) == 5 {
                    v_fn_2080_ = lean_ctor_get(v_x_2079_, 0);
                    lean_inc_ref(v_fn_2080_);
                    if lean_obj_tag(v_fn_2080_) == 5 {
                        v_fn_2081_ = lean_ctor_get(v_fn_2080_, 0);
                        lean_inc_ref(v_fn_2081_);
                        if lean_obj_tag(v_fn_2081_) == 4 {
                            v_declName_2082_ = lean_ctor_get(v_fn_2081_, 0);
                            lean_inc(v_declName_2082_);
                            if lean_obj_tag(v_declName_2082_) == 1 {
                                v_pre_2083_ = lean_ctor_get(v_declName_2082_, 0);
                                lean_inc(v_pre_2083_);
                                if lean_obj_tag(v_pre_2083_) == 1 {
                                    v_pre_2084_ = lean_ctor_get(v_pre_2083_, 0);
                                    lean_inc(v_pre_2084_);
                                    if lean_obj_tag(v_pre_2084_) == 1 {
                                        v_pre_2085_ = lean_ctor_get(v_pre_2084_, 0);
                                        lean_inc(v_pre_2085_);
                                        if lean_obj_tag(v_pre_2085_) == 1 {
                                            v_pre_2086_ = lean_ctor_get(v_pre_2085_, 0);
                                            if lean_obj_tag(v_pre_2086_) == 0 {
                                                v_arg_2087_ = lean_ctor_get(v_x_2079_, 1);
                                                lean_inc_ref(v_arg_2087_);
                                                lean_dec_ref_known(v_x_2079_, 2);
                                                v_arg_2088_ = lean_ctor_get(v_fn_2080_, 1);
                                                lean_inc_ref(v_arg_2088_);
                                                lean_dec_ref_known(v_fn_2080_, 2);
                                                v_us_2089_ = lean_ctor_get(v_fn_2081_, 1);
                                                lean_inc(v_us_2089_);
                                                lean_dec_ref_known(v_fn_2081_, 2);
                                                v_str_2090_ = lean_ctor_get(v_declName_2082_, 1);
                                                lean_inc_ref(v_str_2090_);
                                                lean_dec_ref_known(v_declName_2082_, 2);
                                                v_str_2091_ = lean_ctor_get(v_pre_2083_, 1);
                                                lean_inc_ref(v_str_2091_);
                                                lean_dec_ref_known(v_pre_2083_, 2);
                                                v_str_2092_ = lean_ctor_get(v_pre_2084_, 1);
                                                lean_inc_ref(v_str_2092_);
                                                lean_dec_ref_known(v_pre_2084_, 2);
                                                v_str_2093_ = lean_ctor_get(v_pre_2085_, 1);
                                                lean_inc_ref(v_str_2093_);
                                                lean_dec_ref_known(v_pre_2085_, 2);
                                                v___x_2094_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__0;
                                                v___x_2095_ =
                                                    lean_string_dec_eq(v_str_2093_, v___x_2094_);
                                                lean_dec_ref(v_str_2093_);
                                                if v___x_2095_ == 0 {
                                                    lean_dec_ref(v_str_2092_);
                                                    lean_dec_ref(v_str_2091_);
                                                    lean_dec_ref(v_str_2090_);
                                                    lean_dec(v_us_2089_);
                                                    lean_dec_ref(v_arg_2088_);
                                                    lean_dec_ref(v_arg_2087_);
                                                    v___x_2096_ = lean_box(0);
                                                    return v___x_2096_;
                                                } else {
                                                    v___x_2097_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__1;
                                                    v___x_2098_ = lean_string_dec_eq(
                                                        v_str_2092_,
                                                        v___x_2097_,
                                                    );
                                                    lean_dec_ref(v_str_2092_);
                                                    if v___x_2098_ == 0 {
                                                        lean_dec_ref(v_str_2091_);
                                                        lean_dec_ref(v_str_2090_);
                                                        lean_dec(v_us_2089_);
                                                        lean_dec_ref(v_arg_2088_);
                                                        lean_dec_ref(v_arg_2087_);
                                                        v___x_2099_ = lean_box(0);
                                                        return v___x_2099_;
                                                    } else {
                                                        v___x_2100_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkType___closed__2;
                                                        v___x_2101_ = lean_string_dec_eq(
                                                            v_str_2091_,
                                                            v___x_2100_,
                                                        );
                                                        lean_dec_ref(v_str_2091_);
                                                        if v___x_2101_ == 0 {
                                                            lean_dec_ref(v_str_2090_);
                                                            lean_dec(v_us_2089_);
                                                            lean_dec_ref(v_arg_2088_);
                                                            lean_dec_ref(v_arg_2087_);
                                                            v___x_2102_ = lean_box(0);
                                                            return v___x_2102_;
                                                        } else {
                                                            v___x_2103_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure___closed__0;
                                                            v___x_2104_ = lean_string_dec_eq(
                                                                v_str_2090_,
                                                                v___x_2103_,
                                                            );
                                                            lean_dec_ref(v_str_2090_);
                                                            if v___x_2104_ == 0 {
                                                                lean_dec(v_us_2089_);
                                                                lean_dec_ref(v_arg_2088_);
                                                                lean_dec_ref(v_arg_2087_);
                                                                v___x_2105_ = lean_box(0);
                                                                return v___x_2105_;
                                                            } else {
                                                                if lean_obj_tag(v_us_2089_) == 1 {
                                                                    v_tail_2106_ = lean_ctor_get(
                                                                        v_us_2089_, 1,
                                                                    );
                                                                    if lean_obj_tag(v_tail_2106_)
                                                                        == 0
                                                                    {
                                                                        v_head_2107_ =
                                                                            lean_ctor_get(
                                                                                v_us_2089_, 0,
                                                                            );
                                                                        v_isSharedCheck_2116_ =
                                                                            (!lean_is_exclusive(
                                                                                v_us_2089_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_2116_
                                                                            == 0
                                                                        {
                                                                            v_unused_2117_ =
                                                                                lean_ctor_get(
                                                                                    v_us_2089_, 1,
                                                                                );
                                                                            lean_dec(
                                                                                v_unused_2117_,
                                                                            );
                                                                            v___x_2109_ =
                                                                                v_us_2089_;
                                                                            v_isShared_2110_ = v_isSharedCheck_2116_;
                                                                            state = 1;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_head_2107_);
                                                                            lean_dec(v_us_2089_);
                                                                            v___x_2109_ =
                                                                                lean_box(0);
                                                                            v_isShared_2110_ = v_isSharedCheck_2116_;
                                                                            state = 1;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref_known(
                                                                            v_us_2089_, 2,
                                                                        );
                                                                        lean_dec_ref(v_arg_2088_);
                                                                        lean_dec_ref(v_arg_2087_);
                                                                        v___x_2118_ = lean_box(0);
                                                                        return v___x_2118_;
                                                                    }
                                                                } else {
                                                                    lean_dec(v_us_2089_);
                                                                    lean_dec_ref(v_arg_2088_);
                                                                    lean_dec_ref(v_arg_2087_);
                                                                    v___x_2119_ = lean_box(0);
                                                                    return v___x_2119_;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref_known(v_pre_2085_, 2);
                                                lean_dec_ref_known(v_pre_2084_, 2);
                                                lean_dec_ref_known(v_pre_2083_, 2);
                                                lean_dec_ref_known(v_declName_2082_, 2);
                                                lean_dec_ref_known(v_fn_2081_, 2);
                                                lean_dec_ref_known(v_fn_2080_, 2);
                                                lean_dec_ref_known(v_x_2079_, 2);
                                                v___x_2120_ = lean_box(0);
                                                return v___x_2120_;
                                            }
                                        } else {
                                            lean_dec(v_pre_2085_);
                                            lean_dec_ref_known(v_pre_2084_, 2);
                                            lean_dec_ref_known(v_pre_2083_, 2);
                                            lean_dec_ref_known(v_declName_2082_, 2);
                                            lean_dec_ref_known(v_fn_2081_, 2);
                                            lean_dec_ref_known(v_fn_2080_, 2);
                                            lean_dec_ref_known(v_x_2079_, 2);
                                            v___x_2121_ = lean_box(0);
                                            return v___x_2121_;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_pre_2083_, 2);
                                        lean_dec(v_pre_2084_);
                                        lean_dec_ref_known(v_declName_2082_, 2);
                                        lean_dec_ref_known(v_fn_2081_, 2);
                                        lean_dec_ref_known(v_fn_2080_, 2);
                                        lean_dec_ref_known(v_x_2079_, 2);
                                        v___x_2122_ = lean_box(0);
                                        return v___x_2122_;
                                    }
                                } else {
                                    lean_dec(v_pre_2083_);
                                    lean_dec_ref_known(v_declName_2082_, 2);
                                    lean_dec_ref_known(v_fn_2081_, 2);
                                    lean_dec_ref_known(v_fn_2080_, 2);
                                    lean_dec_ref_known(v_x_2079_, 2);
                                    v___x_2123_ = lean_box(0);
                                    return v___x_2123_;
                                }
                            } else {
                                lean_dec(v_declName_2082_);
                                lean_dec_ref_known(v_fn_2081_, 2);
                                lean_dec_ref_known(v_fn_2080_, 2);
                                lean_dec_ref_known(v_x_2079_, 2);
                                v___x_2124_ = lean_box(0);
                                return v___x_2124_;
                            }
                        } else {
                            lean_dec_ref(v_fn_2081_);
                            lean_dec_ref_known(v_fn_2080_, 2);
                            lean_dec_ref_known(v_x_2079_, 2);
                            v___x_2125_ = lean_box(0);
                            return v___x_2125_;
                        }
                    } else {
                        lean_dec_ref_known(v_x_2079_, 2);
                        lean_dec_ref(v_fn_2080_);
                        v___x_2126_ = lean_box(0);
                        return v___x_2126_;
                    }
                } else {
                    lean_dec_ref(v_x_2079_);
                    v___x_2127_ = lean_box(0);
                    return v___x_2127_;
                }
            }
            1 => {
                if v_isShared_2110_ == 0 {
                    lean_ctor_set_tag(v___x_2109_, 0);
                    lean_ctor_set(v___x_2109_, 1, v_arg_2087_);
                    lean_ctor_set(v___x_2109_, 0, v_arg_2088_);
                    v___x_2112_ = v___x_2109_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_arg_2088_);
                    lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_arg_2087_);
                    v___x_2112_ = v_reuseFailAlloc_2115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2113_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2113_, 0, v_head_2107_);
                lean_ctor_set(v___x_2113_, 1, v___x_2112_);
                v___x_2114_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2() -> *mut LeanObject {
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    v___x_2135_ = lean_box(0);
    v___x_2136_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__1;
    v___x_2137_ = l_Lean_mkConst(v___x_2136_, v___x_2135_);
    return v___x_2137_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(
    mut v_u_2138_: *mut LeanObject,
    mut v_00_u03c3s_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    v___x_2140_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName;
    v___x_2141_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2_once),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__2,
    );
    v___x_2142_ =
        l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_2138_, v_00_u03c3s_2139_, v___x_2141_);
    v___x_2143_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2143_, 0, v___x_2140_);
    lean_ctor_set(v___x_2143_, 1, v___x_2140_);
    lean_ctor_set(v___x_2143_, 2, v___x_2142_);
    v___x_2144_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(
    mut v_e_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2152_: u8 = 0;
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2159_: u8 = 0;
    let mut v_snd_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v_str_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: u8 = 0;
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2179_: u8 = 0;
    let mut v_unused_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2146_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_2145_);
                if lean_obj_tag(v___x_2146_) == 0 {
                    v___x_2147_ = lean_box(0);
                    return v___x_2147_;
                } else {
                    v_val_2148_ = lean_ctor_get(v___x_2146_, 0);
                    lean_inc(v_val_2148_);
                    lean_dec_ref_known(v___x_2146_, 1);
                    v_name_2149_ = lean_ctor_get(v_val_2148_, 0);
                    lean_inc(v_name_2149_);
                    v_p_2150_ = lean_ctor_get(v_val_2148_, 2);
                    lean_inc_ref(v_p_2150_);
                    lean_dec(v_val_2148_);
                    v___x_2185_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHypName;
                    v___x_2186_ = lean_name_eq(v_name_2149_, v___x_2185_);
                    if v___x_2186_ == 0 {
                        v___x_2187_ = l_Lean_Name_hasMacroScopes(v_name_2149_);
                        lean_dec(v_name_2149_);
                        v___y_2152_ = v___x_2187_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_name_2149_);
                        v___y_2152_ = v___x_2186_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2152_ == 0 {
                    lean_dec_ref(v_p_2150_);
                    v___x_2153_ = lean_box(0);
                    return v___x_2153_;
                } else {
                    v___x_2154_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_isPure_x3f(v_p_2150_);
                    if lean_obj_tag(v___x_2154_) == 0 {
                        v___x_2155_ = lean_box(0);
                        return v___x_2155_;
                    } else {
                        v_val_2156_ = lean_ctor_get(v___x_2154_, 0);
                        v_isSharedCheck_2184_ = (!lean_is_exclusive(v___x_2154_)) as u8;
                        if v_isSharedCheck_2184_ == 0 {
                            v___x_2158_ = v___x_2154_;
                            v_isShared_2159_ = v_isSharedCheck_2184_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_2156_);
                            lean_dec(v___x_2154_);
                            v___x_2158_ = lean_box(0);
                            v_isShared_2159_ = v_isSharedCheck_2184_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_snd_2160_ = lean_ctor_get(v_val_2156_, 1);
                lean_inc(v_snd_2160_);
                v_snd_2161_ = lean_ctor_get(v_snd_2160_, 1);
                if lean_obj_tag(v_snd_2161_) == 4 {
                    v_declName_2162_ = lean_ctor_get(v_snd_2161_, 0);
                    lean_inc(v_declName_2162_);
                    if lean_obj_tag(v_declName_2162_) == 1 {
                        v_pre_2163_ = lean_ctor_get(v_declName_2162_, 0);
                        if lean_obj_tag(v_pre_2163_) == 0 {
                            v_fst_2164_ = lean_ctor_get(v_val_2156_, 0);
                            lean_inc(v_fst_2164_);
                            lean_dec(v_val_2156_);
                            v_fst_2165_ = lean_ctor_get(v_snd_2160_, 0);
                            v_isSharedCheck_2179_ = (!lean_is_exclusive(v_snd_2160_)) as u8;
                            if v_isSharedCheck_2179_ == 0 {
                                v_unused_2180_ = lean_ctor_get(v_snd_2160_, 1);
                                lean_dec(v_unused_2180_);
                                v___x_2167_ = v_snd_2160_;
                                v_isShared_2168_ = v_isSharedCheck_2179_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_fst_2165_);
                                lean_dec(v_snd_2160_);
                                v___x_2167_ = lean_box(0);
                                v_isShared_2168_ = v_isSharedCheck_2179_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_declName_2162_, 2);
                            lean_dec(v_snd_2160_);
                            lean_del_object(v___x_2158_);
                            lean_dec(v_val_2156_);
                            v___x_2181_ = lean_box(0);
                            return v___x_2181_;
                        }
                    } else {
                        lean_dec(v_declName_2162_);
                        lean_dec(v_snd_2160_);
                        lean_del_object(v___x_2158_);
                        lean_dec(v_val_2156_);
                        v___x_2182_ = lean_box(0);
                        return v___x_2182_;
                    }
                } else {
                    lean_dec(v_snd_2160_);
                    lean_del_object(v___x_2158_);
                    lean_dec(v_val_2156_);
                    v___x_2183_ = lean_box(0);
                    return v___x_2183_;
                }
            }
            3 => {
                v_str_2169_ = lean_ctor_get(v_declName_2162_, 1);
                lean_inc_ref(v_str_2169_);
                lean_dec_ref_known(v_declName_2162_, 2);
                v___x_2170_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp___closed__0;
                v___x_2171_ = lean_string_dec_eq(v_str_2169_, v___x_2170_);
                lean_dec_ref(v_str_2169_);
                if v___x_2171_ == 0 {
                    lean_del_object(v___x_2167_);
                    lean_dec(v_fst_2165_);
                    lean_dec(v_fst_2164_);
                    lean_del_object(v___x_2158_);
                    v___x_2172_ = lean_box(0);
                    return v___x_2172_;
                } else {
                    if v_isShared_2168_ == 0 {
                        lean_ctor_set(v___x_2167_, 1, v_fst_2165_);
                        lean_ctor_set(v___x_2167_, 0, v_fst_2164_);
                        v___x_2174_ = v___x_2167_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_fst_2164_);
                        lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_fst_2165_);
                        v___x_2174_ = v_reuseFailAlloc_2178_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2159_ == 0 {
                    lean_ctor_set(v___x_2158_, 0, v___x_2174_);
                    v___x_2176_ = v___x_2158_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2174_);
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
    mut v_pos_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    v___x_2189_ = lean_unsigned_to_nat(3);
    v___x_2190_ = lean_unsigned_to_nat(1);
    v___x_2191_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_2189_, v___x_2190_, v_pos_2188_);
    return v___x_2191_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct___boxed(
    mut v_pos_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2193_: *mut LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_pos_2192_);
    lean_dec(v_pos_2192_);
    return v_res_2193_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(
    mut v_pos_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    v___x_2195_ = lean_unsigned_to_nat(3);
    v___x_2196_ = lean_unsigned_to_nat(2);
    v___x_2197_ = l_Lean_SubExpr_Pos_pushNaryArg(v___x_2195_, v___x_2196_, v_pos_2194_);
    return v___x_2197_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct___boxed(
    mut v_pos_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2199_: *mut LeanObject = core::ptr::null_mut();
    v_res_2199_ = l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_pos_2198_);
    lean_dec(v_pos_2198_);
    return v_res_2199_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
    mut v_u_2206_: *mut LeanObject,
    mut v_00_u03c3s_2207_: *mut LeanObject,
    mut v_lhs_2208_: *mut LeanObject,
    mut v_rhs_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    v___x_2210_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1;
    v___x_2211_ = lean_box(0);
    v___x_2212_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2212_, 0, v_u_2206_);
    lean_ctor_set(v___x_2212_, 1, v___x_2211_);
    v___x_2213_ = l_Lean_mkConst(v___x_2210_, v___x_2212_);
    v___x_2214_ = l_Lean_mkApp3(v___x_2213_, v_00_u03c3s_2207_, v_lhs_2208_, v_rhs_2209_);
    return v___x_2214_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
    mut v_u_2235_: *mut LeanObject,
    mut v_00_u03c3s_2236_: *mut LeanObject,
    mut v_lhs_2237_: *mut LeanObject,
    mut v_rhs_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_lhs_2237_);
    v___x_2239_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_lhs_2237_);
    if lean_obj_tag(v___x_2239_) == 1 {
        let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2239_, 1);
        lean_dec_ref(v_lhs_2237_);
        v___x_2240_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__1;
        v___x_2241_ = lean_box(0);
        v___x_2242_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_2242_, 0, v_u_2235_);
        lean_ctor_set(v___x_2242_, 1, v___x_2241_);
        v___x_2243_ = l_Lean_mkConst(v___x_2240_, v___x_2242_);
        lean_inc_ref(v_rhs_2238_);
        v___x_2244_ = l_Lean_mkAppB(v___x_2243_, v_00_u03c3s_2236_, v_rhs_2238_);
        v___x_2245_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2245_, 0, v_rhs_2238_);
        lean_ctor_set(v___x_2245_, 1, v___x_2244_);
        return v___x_2245_;
    } else {
        let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2239_);
        lean_inc_ref(v_rhs_2238_);
        v___x_2246_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_rhs_2238_);
        if lean_obj_tag(v___x_2246_) == 1 {
            let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_2246_, 1);
            lean_dec_ref(v_rhs_2238_);
            v___x_2247_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__3;
            v___x_2248_ = lean_box(0);
            v___x_2249_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2249_, 0, v_u_2235_);
            lean_ctor_set(v___x_2249_, 1, v___x_2248_);
            v___x_2250_ = l_Lean_mkConst(v___x_2247_, v___x_2249_);
            lean_inc_ref(v_lhs_2237_);
            v___x_2251_ = l_Lean_mkAppB(v___x_2250_, v_00_u03c3s_2236_, v_lhs_2237_);
            v___x_2252_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2252_, 0, v_lhs_2237_);
            lean_ctor_set(v___x_2252_, 1, v___x_2251_);
            return v___x_2252_;
        } else {
            let mut v_result_2253_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2246_);
            lean_inc_ref(v_00_u03c3s_2236_);
            lean_inc(v_u_2235_);
            v_result_2253_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                v_u_2235_,
                v_00_u03c3s_2236_,
                v_lhs_2237_,
                v_rhs_2238_,
            );
            v___x_2254_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd___closed__6;
            v___x_2255_ = lean_box(0);
            v___x_2256_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_2256_, 0, v_u_2235_);
            lean_ctor_set(v___x_2256_, 1, v___x_2255_);
            v___x_2257_ = l_Lean_mkConst(v___x_2254_, v___x_2256_);
            lean_inc_ref(v_result_2253_);
            v___x_2258_ = l_Lean_mkAppB(v___x_2257_, v_00_u03c3s_2236_, v_result_2253_);
            v___x_2259_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_2259_, 0, v_result_2253_);
            lean_ctor_set(v___x_2259_, 1, v___x_2258_);
            return v___x_2259_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(
    mut v_u_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType___closed__1;
    v___x_2265_ = l_Lean_Level_succ___override(v_u_2263_);
    v___x_2266_ = lean_box(0);
    lean_inc(v___x_2265_);
    v___x_2267_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2267_, 0, v___x_2265_);
    lean_ctor_set(v___x_2267_, 1, v___x_2266_);
    v___x_2268_ = l_Lean_mkConst(v___x_2264_, v___x_2267_);
    v___x_2269_ = l_Lean_mkSort(v___x_2265_);
    v___x_2270_ = l_Lean_Expr_app___override(v___x_2268_, v___x_2269_);
    return v___x_2270_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil(
    mut v_u_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkNil___closed__1;
    v___x_2277_ = l_Lean_Level_succ___override(v_u_2275_);
    v___x_2278_ = lean_box(0);
    lean_inc(v___x_2277_);
    v___x_2279_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2279_, 0, v___x_2277_);
    lean_ctor_set(v___x_2279_, 1, v___x_2278_);
    v___x_2280_ = l_Lean_mkConst(v___x_2276_, v___x_2279_);
    v___x_2281_ = l_Lean_mkSort(v___x_2277_);
    v___x_2282_ = l_Lean_Expr_app___override(v___x_2280_, v___x_2281_);
    return v___x_2282_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons(
    mut v_u_2287_: *mut LeanObject,
    mut v_hd_2288_: *mut LeanObject,
    mut v_tl_2289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    v___x_2290_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1;
    v___x_2291_ = l_Lean_Level_succ___override(v_u_2287_);
    v___x_2292_ = lean_box(0);
    lean_inc(v___x_2291_);
    v___x_2293_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2293_, 0, v___x_2291_);
    lean_ctor_set(v___x_2293_, 1, v___x_2292_);
    v___x_2294_ = l_Lean_mkConst(v___x_2290_, v___x_2293_);
    v___x_2295_ = l_Lean_mkSort(v___x_2291_);
    v___x_2296_ = l_Lean_mkApp3(v___x_2294_, v___x_2295_, v_hd_2288_, v_tl_2289_);
    return v___x_2296_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(
    mut v_a_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2331_: u8 = 0;
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2335_: u8 = 0;
    let mut v_isSharedCheck_2336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2303_ = lean_ctor_get(v_a_2297_, 0);
                v_snd_2304_ = lean_ctor_get(v_a_2297_, 1);
                v_isSharedCheck_2336_ = (!lean_is_exclusive(v_a_2297_)) as u8;
                if v_isSharedCheck_2336_ == 0 {
                    v___x_2306_ = v_a_2297_;
                    v_isShared_2307_ = v_isSharedCheck_2336_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2304_);
                    lean_inc(v_fst_2303_);
                    lean_dec(v_a_2297_);
                    v___x_2306_ = lean_box(0);
                    v_isShared_2307_ = v_isSharedCheck_2336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2308_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1;
                v___x_2309_ = lean_unsigned_to_nat(3);
                v___x_2310_ = l_Lean_Expr_isAppOfArity(v_fst_2303_, v___x_2308_, v___x_2309_);
                if v___x_2310_ == 0 {
                    if v_isShared_2307_ == 0 {
                        v___x_2312_ = v___x_2306_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_fst_2303_);
                        lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_snd_2304_);
                        v___x_2312_ = v_reuseFailAlloc_2314_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2315_ = lean_unsigned_to_nat(2);
                    v___x_2316_ = l_Lean_Expr_getAppNumArgs(v_fst_2303_);
                    v___x_2317_ = lean_nat_sub(v___x_2316_, v___x_2315_);
                    lean_dec(v___x_2316_);
                    v___x_2318_ = lean_unsigned_to_nat(1);
                    v___x_2319_ = lean_nat_sub(v___x_2317_, v___x_2318_);
                    lean_dec(v___x_2317_);
                    v___x_2320_ = l_Lean_Expr_getRevArg_x21(v_fst_2303_, v___x_2319_);
                    lean_dec(v_fst_2303_);
                    v___x_2321_ = l_Lean_Meta_whnfR(
                        v___x_2320_,
                        v___y_2298_,
                        v___y_2299_,
                        v___y_2300_,
                        v___y_2301_,
                    );
                    if lean_obj_tag(v___x_2321_) == 0 {
                        v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
                        lean_inc(v_a_2322_);
                        lean_dec_ref_known(v___x_2321_, 1);
                        v___x_2323_ = lean_nat_add(v_snd_2304_, v___x_2318_);
                        lean_dec(v_snd_2304_);
                        if v_isShared_2307_ == 0 {
                            lean_ctor_set(v___x_2306_, 1, v___x_2323_);
                            lean_ctor_set(v___x_2306_, 0, v_a_2322_);
                            v___x_2325_ = v___x_2306_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2322_);
                            lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2323_);
                            v___x_2325_ = v_reuseFailAlloc_2327_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2306_);
                        lean_dec(v_snd_2304_);
                        v_a_2328_ = lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2335_ = (!lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2335_ == 0 {
                            v___x_2330_ = v___x_2321_;
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2328_);
                            lean_dec(v___x_2321_);
                            v___x_2330_ = lean_box(0);
                            v_isShared_2331_ = v_isSharedCheck_2335_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_2313_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2313_, 0, v___x_2312_);
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
                    v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
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
    mut v_a_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2343_: *mut LeanObject = core::ptr::null_mut();
    v_res_2343_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
    lean_dec(v___y_2341_);
    lean_dec_ref(v___y_2340_);
    lean_dec(v___y_2339_);
    lean_dec_ref(v___y_2338_);
    return v_res_2343_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(
    mut v_00_u03c3s_2344_: *mut LeanObject,
    mut v_a_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
    mut v_a_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2358_: u8 = 0;
    let mut v_snd_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_a_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_a_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2350_) == 0 {
                    v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
                    lean_inc(v_a_2351_);
                    lean_dec_ref_known(v___x_2350_, 1);
                    v___x_2352_ = lean_unsigned_to_nat(0);
                    v___x_2353_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2353_, 0, v_a_2351_);
                    lean_ctor_set(v___x_2353_, 1, v___x_2352_);
                    v___x_2354_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v___x_2353_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
                    if lean_obj_tag(v___x_2354_) == 0 {
                        v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2363_ = (!lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2363_ == 0 {
                            v___x_2357_ = v___x_2354_;
                            v_isShared_2358_ = v_isSharedCheck_2363_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2355_);
                            lean_dec(v___x_2354_);
                            v___x_2357_ = lean_box(0);
                            v_isShared_2358_ = v_isSharedCheck_2363_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2364_ = lean_ctor_get(v___x_2354_, 0);
                        v_isSharedCheck_2371_ = (!lean_is_exclusive(v___x_2354_)) as u8;
                        if v_isSharedCheck_2371_ == 0 {
                            v___x_2366_ = v___x_2354_;
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2364_);
                            lean_dec(v___x_2354_);
                            v___x_2366_ = lean_box(0);
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2372_ = lean_ctor_get(v___x_2350_, 0);
                    v_isSharedCheck_2379_ = (!lean_is_exclusive(v___x_2350_)) as u8;
                    if v_isSharedCheck_2379_ == 0 {
                        v___x_2374_ = v___x_2350_;
                        v_isShared_2375_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2372_);
                        lean_dec(v___x_2350_);
                        v___x_2374_ = lean_box(0);
                        v_isShared_2375_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2359_ = lean_ctor_get(v_a_2355_, 1);
                lean_inc(v_snd_2359_);
                lean_dec(v_a_2355_);
                if v_isShared_2358_ == 0 {
                    lean_ctor_set(v___x_2357_, 0, v_snd_2359_);
                    v___x_2361_ = v___x_2357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_snd_2359_);
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
                    v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
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
                    v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
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
    mut v_00_u03c3s_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
    mut v_a_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2386_: *mut LeanObject = core::ptr::null_mut();
    v_res_2386_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_length(
        v_00_u03c3s_2380_,
        v_a_2381_,
        v_a_2382_,
        v_a_2383_,
        v_a_2384_,
    );
    lean_dec(v_a_2384_);
    lean_dec_ref(v_a_2383_);
    lean_dec(v_a_2382_);
    lean_dec_ref(v_a_2381_);
    return v_res_2386_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(
    mut v_inst_2387_: *mut LeanObject,
    mut v_a_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    v___x_2394_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___redArg(v_a_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
    return v___x_2394_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0___boxed(
    mut v_inst_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v___y_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2402_: *mut LeanObject = core::ptr::null_mut();
    v_res_2402_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_Do_ProofMode_TypeList_length_spec__0(v_inst_2395_, v_a_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
    lean_dec(v___y_2400_);
    lean_dec_ref(v___y_2399_);
    lean_dec(v___y_2398_);
    lean_dec_ref(v___y_2397_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(
    mut v_e_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u8 = 0;
    v___x_2404_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21___closed__1;
    v___x_2405_ = lean_unsigned_to_nat(3);
    v___x_2406_ = l_Lean_Expr_isAppOfArity(v_e_2403_, v___x_2404_, v___x_2405_);
    if v___x_2406_ == 0 {
        let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
        v___x_2407_ = lean_box(0);
        return v___x_2407_;
    } else {
        let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
        v___x_2408_ = lean_box(0);
        v___x_2409_ = l_Lean_Expr_appFn_x21(v_e_2403_);
        v___x_2410_ = l_Lean_Expr_appFn_x21(v___x_2409_);
        v___x_2411_ = l_Lean_Expr_appArg_x21(v___x_2410_);
        lean_dec_ref(v___x_2410_);
        v___x_2412_ = l_Lean_Expr_appArg_x21(v___x_2409_);
        lean_dec_ref(v___x_2409_);
        v___x_2413_ = l_Lean_Expr_appArg_x21(v_e_2403_);
        v___x_2414_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2414_, 0, v___x_2412_);
        lean_ctor_set(v___x_2414_, 1, v___x_2413_);
        v___x_2415_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2415_, 0, v___x_2411_);
        lean_ctor_set(v___x_2415_, 1, v___x_2414_);
        v___x_2416_ = l_Lean_Expr_getAppFn(v_e_2403_);
        v___x_2417_ = l_Lean_Expr_constLevels_x21(v___x_2416_);
        lean_dec_ref(v___x_2416_);
        v___x_2418_ = lean_unsigned_to_nat(0);
        v___x_2419_ = l_List_get_x21Internal___redArg(v___x_2408_, v___x_2417_, v___x_2418_);
        lean_dec(v___x_2417_);
        v___x_2420_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2420_, 0, v___x_2419_);
        lean_ctor_set(v___x_2420_, 1, v___x_2415_);
        v___x_2421_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2421_, 0, v___x_2420_);
        return v___x_2421_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f___boxed(
    mut v_e_2422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2423_: *mut LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_2422_);
    lean_dec_ref(v_e_2422_);
    return v_res_2423_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2()
-> *mut LeanObject {
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    v___x_2427_ = lean_box(0);
    v___x_2428_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__1;
    v___x_2429_ = l_Lean_Expr_const___override(v___x_2428_, v___x_2427_);
    return v___x_2429_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__3()
-> *mut LeanObject {
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    v___x_2430_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default___closed__2,
    );
    v___x_2431_ = lean_box(0);
    v___x_2432_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2432_, 0, v___x_2431_);
    lean_ctor_set(v___x_2432_, 1, v___x_2430_);
    lean_ctor_set(v___x_2432_, 2, v___x_2430_);
    lean_ctor_set(v___x_2432_, 3, v___x_2430_);
    return v___x_2432_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default() -> *mut LeanObject
{
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    v___x_2433_ = lean_obj_once(
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
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal() -> *mut LeanObject {
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    v___x_2434_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default;
    return v___x_2434_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(
    mut v_expr_2442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: u8 = 0;
    v___x_2443_ = l_Lean_Expr_consumeMData(v_expr_2442_);
    v___x_2444_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2;
    v___x_2445_ = lean_unsigned_to_nat(3);
    v___x_2446_ = l_Lean_Expr_isAppOfArity(v___x_2443_, v___x_2444_, v___x_2445_);
    if v___x_2446_ == 0 {
        let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2443_);
        v___x_2447_ = lean_box(0);
        return v___x_2447_;
    } else {
        let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
        v___x_2448_ = lean_box(0);
        v___x_2449_ = l_Lean_Expr_appFn_x21(v___x_2443_);
        v___x_2450_ = l_Lean_Expr_appFn_x21(v___x_2449_);
        v___x_2451_ = l_Lean_Expr_appArg_x21(v___x_2450_);
        lean_dec_ref(v___x_2450_);
        v___x_2452_ = l_Lean_Expr_appArg_x21(v___x_2449_);
        lean_dec_ref(v___x_2449_);
        v___x_2453_ = l_Lean_Expr_appArg_x21(v___x_2443_);
        lean_dec_ref(v___x_2443_);
        v___x_2454_ = l_Lean_Expr_getAppFn_x27(v_expr_2442_);
        v___x_2455_ = l_Lean_Expr_constLevels_x21(v___x_2454_);
        lean_dec_ref(v___x_2454_);
        v___x_2456_ = lean_unsigned_to_nat(0);
        v___x_2457_ = l_List_get_x21Internal___redArg(v___x_2448_, v___x_2455_, v___x_2456_);
        lean_dec(v___x_2455_);
        v___x_2458_ = lean_alloc_ctor(0, 4, (0) as u32);
        lean_ctor_set(v___x_2458_, 0, v___x_2457_);
        lean_ctor_set(v___x_2458_, 1, v___x_2451_);
        lean_ctor_set(v___x_2458_, 2, v___x_2452_);
        lean_ctor_set(v___x_2458_, 3, v___x_2453_);
        v___x_2459_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2459_, 0, v___x_2458_);
        return v___x_2459_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___boxed(
    mut v_expr_2460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2461_: *mut LeanObject = core::ptr::null_mut();
    v_res_2461_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_expr_2460_);
    lean_dec_ref(v_expr_2460_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(
    mut v_e_2462_: *mut LeanObject,
    mut v___y_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2479_: u8 = 0;
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2485_: u8 = 0;
    let mut v_unused_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = l_Lean_Expr_hasMVar(v_e_2462_);
                if v___x_2465_ == 0 {
                    v___x_2466_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2466_, 0, v_e_2462_);
                    return v___x_2466_;
                } else {
                    v___x_2467_ = lean_st_ref_get(v___y_2463_);
                    v_mctx_2468_ = lean_ctor_get(v___x_2467_, 0);
                    lean_inc_ref(v_mctx_2468_);
                    lean_dec(v___x_2467_);
                    v___x_2469_ = l_Lean_instantiateMVarsCore(v_mctx_2468_, v_e_2462_);
                    v_fst_2470_ = lean_ctor_get(v___x_2469_, 0);
                    lean_inc(v_fst_2470_);
                    v_snd_2471_ = lean_ctor_get(v___x_2469_, 1);
                    lean_inc(v_snd_2471_);
                    lean_dec_ref(v___x_2469_);
                    v___x_2472_ = lean_st_ref_take(v___y_2463_);
                    v_cache_2473_ = lean_ctor_get(v___x_2472_, 1);
                    v_zetaDeltaFVarIds_2474_ = lean_ctor_get(v___x_2472_, 2);
                    v_postponed_2475_ = lean_ctor_get(v___x_2472_, 3);
                    v_diag_2476_ = lean_ctor_get(v___x_2472_, 4);
                    v_isSharedCheck_2485_ = (!lean_is_exclusive(v___x_2472_)) as u8;
                    if v_isSharedCheck_2485_ == 0 {
                        v_unused_2486_ = lean_ctor_get(v___x_2472_, 0);
                        lean_dec(v_unused_2486_);
                        v___x_2478_ = v___x_2472_;
                        v_isShared_2479_ = v_isSharedCheck_2485_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2476_);
                        lean_inc(v_postponed_2475_);
                        lean_inc(v_zetaDeltaFVarIds_2474_);
                        lean_inc(v_cache_2473_);
                        lean_dec(v___x_2472_);
                        v___x_2478_ = lean_box(0);
                        v_isShared_2479_ = v_isSharedCheck_2485_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2479_ == 0 {
                    lean_ctor_set(v___x_2478_, 0, v_snd_2471_);
                    v___x_2481_ = v___x_2478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_snd_2471_);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_cache_2473_);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_zetaDeltaFVarIds_2474_);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 3, v_postponed_2475_);
                    lean_ctor_set(v_reuseFailAlloc_2484_, 4, v_diag_2476_);
                    v___x_2481_ = v_reuseFailAlloc_2484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2482_ = lean_st_ref_set(v___y_2463_, v___x_2481_);
                v___x_2483_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2483_, 0, v_fst_2470_);
                return v___x_2483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg___boxed(
    mut v_e_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2490_: *mut LeanObject = core::ptr::null_mut();
    v_res_2490_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(
            v_e_2487_,
            v___y_2488_,
        );
    lean_dec(v___y_2488_);
    return v_res_2490_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0(
    mut v_e_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
    mut v___y_2496_: *mut LeanObject,
    mut v___y_2497_: *mut LeanObject,
    mut v___y_2498_: *mut LeanObject,
    mut v___y_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    v___x_2501_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(
            v_e_2491_,
            v___y_2497_,
        );
    return v___x_2501_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___boxed(
    mut v_e_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
    mut v___y_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v___y_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
    mut v___y_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2512_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2510_);
    lean_dec_ref(v___y_2509_);
    lean_dec(v___y_2508_);
    lean_dec_ref(v___y_2507_);
    lean_dec(v___y_2506_);
    lean_dec_ref(v___y_2505_);
    lean_dec(v___y_2504_);
    lean_dec_ref(v___y_2503_);
    return v_res_2512_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(
    mut v_msgData_2513_: *mut LeanObject,
    mut v___y_2514_: *mut LeanObject,
    mut v___y_2515_: *mut LeanObject,
    mut v___y_2516_: *mut LeanObject,
    mut v___y_2517_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    v___x_2519_ = lean_st_ref_get(v___y_2517_);
    v_env_2520_ = lean_ctor_get(v___x_2519_, 0);
    lean_inc_ref(v_env_2520_);
    lean_dec(v___x_2519_);
    v___x_2521_ = lean_st_ref_get(v___y_2515_);
    v_mctx_2522_ = lean_ctor_get(v___x_2521_, 0);
    lean_inc_ref(v_mctx_2522_);
    lean_dec(v___x_2521_);
    v_lctx_2523_ = lean_ctor_get(v___y_2514_, 2);
    v_options_2524_ = lean_ctor_get(v___y_2516_, 2);
    lean_inc_ref(v_options_2524_);
    lean_inc_ref(v_lctx_2523_);
    v___x_2525_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2525_, 0, v_env_2520_);
    lean_ctor_set(v___x_2525_, 1, v_mctx_2522_);
    lean_ctor_set(v___x_2525_, 2, v_lctx_2523_);
    lean_ctor_set(v___x_2525_, 3, v_options_2524_);
    v___x_2526_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2526_, 0, v___x_2525_);
    lean_ctor_set(v___x_2526_, 1, v_msgData_2513_);
    v___x_2527_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2527_, 0, v___x_2526_);
    return v___x_2527_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1___boxed(
    mut v_msgData_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2534_: *mut LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msgData_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
    lean_dec(v___y_2532_);
    lean_dec_ref(v___y_2531_);
    lean_dec(v___y_2530_);
    lean_dec_ref(v___y_2529_);
    return v_res_2534_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(
    mut v_msg_2535_: *mut LeanObject,
    mut v___y_2536_: *mut LeanObject,
    mut v___y_2537_: *mut LeanObject,
    mut v___y_2538_: *mut LeanObject,
    mut v___y_2539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2541_ = lean_ctor_get(v___y_2538_, 5);
                v___x_2542_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
                v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
                v_isSharedCheck_2551_ = (!lean_is_exclusive(v___x_2542_)) as u8;
                if v_isSharedCheck_2551_ == 0 {
                    v___x_2545_ = v___x_2542_;
                    v_isShared_2546_ = v_isSharedCheck_2551_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2543_);
                    lean_dec(v___x_2542_);
                    v___x_2545_ = lean_box(0);
                    v_isShared_2546_ = v_isSharedCheck_2551_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2541_);
                v___x_2547_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2547_, 0, v_ref_2541_);
                lean_ctor_set(v___x_2547_, 1, v_a_2543_);
                if v_isShared_2546_ == 0 {
                    lean_ctor_set_tag(v___x_2545_, 1);
                    lean_ctor_set(v___x_2545_, 0, v___x_2547_);
                    v___x_2549_ = v___x_2545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2547_);
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
    mut v_msg_2552_: *mut LeanObject,
    mut v___y_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2558_: *mut LeanObject = core::ptr::null_mut();
    v_res_2558_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1___redArg(
            v_msg_2552_,
            v___y_2553_,
            v___y_2554_,
            v___y_2555_,
            v___y_2556_,
        );
    lean_dec(v___y_2556_);
    lean_dec_ref(v___y_2555_);
    lean_dec(v___y_2554_);
    lean_dec_ref(v___y_2553_);
    return v_res_2558_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__1() -> *mut LeanObject {
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    v___x_2560_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal___closed__0;
    v___x_2561_ = l_Lean_stringToMessageData(v___x_2560_);
    return v___x_2561_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
    mut v_a_2562_: *mut LeanObject,
    mut v_a_2563_: *mut LeanObject,
    mut v_a_2564_: *mut LeanObject,
    mut v_a_2565_: *mut LeanObject,
    mut v_a_2566_: *mut LeanObject,
    mut v_a_2567_: *mut LeanObject,
    mut v_a_2568_: *mut LeanObject,
    mut v_a_2569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_a_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2592_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2596_: u8 = 0;
    let mut v_a_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2571_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_2563_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_,
                );
                if lean_obj_tag(v___x_2571_) == 0 {
                    v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
                    lean_inc_n(v_a_2572_, 2);
                    lean_dec_ref_known(v___x_2571_, 1);
                    v___x_2573_ = l_Lean_MVarId_getType(
                        v_a_2572_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_,
                    );
                    if lean_obj_tag(v___x_2573_) == 0 {
                        v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
                        lean_inc(v_a_2574_);
                        lean_dec_ref_known(v___x_2573_, 1);
                        v___x_2575_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__0___redArg(v_a_2574_, v_a_2567_);
                        v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
                        v_isSharedCheck_2588_ = (!lean_is_exclusive(v___x_2575_)) as u8;
                        if v_isSharedCheck_2588_ == 0 {
                            v___x_2578_ = v___x_2575_;
                            v_isShared_2579_ = v_isSharedCheck_2588_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2576_);
                            lean_dec(v___x_2575_);
                            v___x_2578_ = lean_box(0);
                            v_isShared_2579_ = v_isSharedCheck_2588_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2572_);
                        v_a_2589_ = lean_ctor_get(v___x_2573_, 0);
                        v_isSharedCheck_2596_ = (!lean_is_exclusive(v___x_2573_)) as u8;
                        if v_isSharedCheck_2596_ == 0 {
                            v___x_2591_ = v___x_2573_;
                            v_isShared_2592_ = v_isSharedCheck_2596_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2589_);
                            lean_dec(v___x_2573_);
                            v___x_2591_ = lean_box(0);
                            v_isShared_2592_ = v_isSharedCheck_2596_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2597_ = lean_ctor_get(v___x_2571_, 0);
                    v_isSharedCheck_2604_ = (!lean_is_exclusive(v___x_2571_)) as u8;
                    if v_isSharedCheck_2604_ == 0 {
                        v___x_2599_ = v___x_2571_;
                        v_isShared_2600_ = v_isSharedCheck_2604_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2597_);
                        lean_dec(v___x_2571_);
                        v___x_2599_ = lean_box(0);
                        v_isShared_2600_ = v_isSharedCheck_2604_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2580_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_2576_);
                lean_dec(v_a_2576_);
                if lean_obj_tag(v___x_2580_) == 1 {
                    v_val_2581_ = lean_ctor_get(v___x_2580_, 0);
                    lean_inc(v_val_2581_);
                    lean_dec_ref_known(v___x_2580_, 1);
                    v___x_2582_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2582_, 0, v_a_2572_);
                    lean_ctor_set(v___x_2582_, 1, v_val_2581_);
                    if v_isShared_2579_ == 0 {
                        lean_ctor_set(v___x_2578_, 0, v___x_2582_);
                        v___x_2584_ = v___x_2578_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
                        v___x_2584_ = v_reuseFailAlloc_2585_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2580_);
                    lean_del_object(v___x_2578_);
                    lean_dec(v_a_2572_);
                    v___x_2586_ = lean_obj_once(
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
                    v_reuseFailAlloc_2595_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
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
                    v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
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
    mut v_a_2605_: *mut LeanObject,
    mut v_a_2606_: *mut LeanObject,
    mut v_a_2607_: *mut LeanObject,
    mut v_a_2608_: *mut LeanObject,
    mut v_a_2609_: *mut LeanObject,
    mut v_a_2610_: *mut LeanObject,
    mut v_a_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v_a_2613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2614_: *mut LeanObject = core::ptr::null_mut();
    v_res_2614_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
        v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_,
    );
    lean_dec(v_a_2612_);
    lean_dec_ref(v_a_2611_);
    lean_dec(v_a_2610_);
    lean_dec_ref(v_a_2609_);
    lean_dec(v_a_2608_);
    lean_dec_ref(v_a_2607_);
    lean_dec(v_a_2606_);
    lean_dec_ref(v_a_2605_);
    return v_res_2614_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1(
    mut v_00_u03b1_2615_: *mut LeanObject,
    mut v_msg_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2627_: *mut LeanObject,
    mut v_msg_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2638_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2636_);
    lean_dec_ref(v___y_2635_);
    lean_dec(v___y_2634_);
    lean_dec_ref(v___y_2633_);
    lean_dec(v___y_2632_);
    lean_dec_ref(v___y_2631_);
    lean_dec(v___y_2630_);
    lean_dec_ref(v___y_2629_);
    return v_res_2638_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(
    mut v_goal_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    v_u_2646_ = lean_ctor_get(v_goal_2645_, 0);
    lean_inc(v_u_2646_);
    v_00_u03c3s_2647_ = lean_ctor_get(v_goal_2645_, 1);
    lean_inc_ref(v_00_u03c3s_2647_);
    v_hyps_2648_ = lean_ctor_get(v_goal_2645_, 2);
    lean_inc_ref(v_hyps_2648_);
    v_target_2649_ = lean_ctor_get(v_goal_2645_, 3);
    lean_inc_ref(v_target_2649_);
    lean_dec_ref(v_goal_2645_);
    v___x_2650_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip___closed__1;
    v___x_2651_ = lean_box(0);
    v___x_2652_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2652_, 0, v_u_2646_);
    lean_ctor_set(v___x_2652_, 1, v___x_2651_);
    v___x_2653_ = l_Lean_mkConst(v___x_2650_, v___x_2652_);
    v___x_2654_ = l_Lean_mkApp3(v___x_2653_, v_00_u03c3s_2647_, v_hyps_2648_, v_target_2649_);
    return v___x_2654_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(
    mut v_goal_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    v_u_2656_ = lean_ctor_get(v_goal_2655_, 0);
    lean_inc(v_u_2656_);
    v_00_u03c3s_2657_ = lean_ctor_get(v_goal_2655_, 1);
    lean_inc_ref(v_00_u03c3s_2657_);
    v_hyps_2658_ = lean_ctor_get(v_goal_2655_, 2);
    lean_inc_ref(v_hyps_2658_);
    v_target_2659_ = lean_ctor_get(v_goal_2655_, 3);
    lean_inc_ref(v_target_2659_);
    lean_dec_ref(v_goal_2655_);
    v___x_2660_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__2;
    v___x_2661_ = lean_box(0);
    v___x_2662_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2662_, 0, v_u_2656_);
    lean_ctor_set(v___x_2662_, 1, v___x_2661_);
    v___x_2663_ = l_Lean_mkConst(v___x_2660_, v___x_2662_);
    v___x_2664_ = l_Lean_mkApp3(v___x_2663_, v_00_u03c3s_2657_, v_hyps_2658_, v_target_2659_);
    return v___x_2664_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(
    mut v_msg_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    v___x_2666_ = lean_box(0);
    v___x_2667_ = lean_panic_fn_borrowed(v___x_2666_, v_msg_2665_);
    return v___x_2667_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3()
-> *mut LeanObject {
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    v___x_2671_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__2;
    v___x_2672_ = lean_unsigned_to_nat(8);
    v___x_2673_ = lean_unsigned_to_nat(141);
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
    mut v_name_2677_: *mut LeanObject,
    mut v_e_2678_: *mut LeanObject,
    mut v_p_2679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2684_: u8 = 0;
    let mut v_name_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: u8 = 0;
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2678_);
                v___x_2680_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_2678_);
                if lean_obj_tag(v___x_2680_) == 1 {
                    lean_dec_ref(v_e_2678_);
                    v_val_2681_ = lean_ctor_get(v___x_2680_, 0);
                    v_isSharedCheck_2692_ = (!lean_is_exclusive(v___x_2680_)) as u8;
                    if v_isSharedCheck_2692_ == 0 {
                        v___x_2683_ = v___x_2680_;
                        v_isShared_2684_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2681_);
                        lean_dec(v___x_2680_);
                        v___x_2683_ = lean_box(0);
                        v_isShared_2684_ = v_isSharedCheck_2692_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2680_);
                    v___x_2693_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_2678_);
                    if lean_obj_tag(v___x_2693_) == 1 {
                        lean_dec_ref(v_e_2678_);
                        v_val_2694_ = lean_ctor_get(v___x_2693_, 0);
                        lean_inc(v_val_2694_);
                        lean_dec_ref_known(v___x_2693_, 1);
                        v_snd_2695_ = lean_ctor_get(v_val_2694_, 1);
                        lean_inc(v_snd_2695_);
                        lean_dec(v_val_2694_);
                        v_snd_2696_ = lean_ctor_get(v_snd_2695_, 1);
                        lean_inc(v_snd_2696_);
                        lean_dec(v_snd_2695_);
                        v_fst_2697_ = lean_ctor_get(v_snd_2696_, 0);
                        lean_inc(v_fst_2697_);
                        v_snd_2698_ = lean_ctor_get(v_snd_2696_, 1);
                        lean_inc(v_snd_2698_);
                        lean_dec(v_snd_2696_);
                        v___x_2699_ = l_Lean_Elab_Tactic_Do_ProofMode_pushLeftConjunct(v_p_2679_);
                        v___x_2700_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_2677_, v_snd_2698_, v___x_2699_);
                        if lean_obj_tag(v___x_2700_) == 0 {
                            v___x_2701_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_pushRightConjunct(v_p_2679_);
                            lean_dec(v_p_2679_);
                            v_e_2678_ = v_fst_2697_;
                            v_p_2679_ = v___x_2701_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_fst_2697_);
                            lean_dec(v_p_2679_);
                            return v___x_2700_;
                        }
                    } else {
                        lean_dec(v___x_2693_);
                        lean_dec(v_p_2679_);
                        v___x_2703_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_2678_);
                        if lean_obj_tag(v___x_2703_) == 1 {
                            lean_dec_ref_known(v___x_2703_, 1);
                            v___x_2704_ = lean_box(0);
                            return v___x_2704_;
                        } else {
                            lean_dec(v___x_2703_);
                            v___x_2705_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go___closed__3);
                            v___x_2706_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go_spec__0(v___x_2705_);
                            return v___x_2706_;
                        }
                    }
                }
            }
            1 => {
                v_name_2685_ = lean_ctor_get(v_val_2681_, 0);
                v___x_2686_ = lean_name_eq(v_name_2685_, v_name_2677_);
                if v___x_2686_ == 0 {
                    lean_del_object(v___x_2683_);
                    lean_dec(v_val_2681_);
                    lean_dec(v_p_2679_);
                    v___x_2687_ = lean_box(0);
                    return v___x_2687_;
                } else {
                    v___x_2688_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2688_, 0, v_p_2679_);
                    lean_ctor_set(v___x_2688_, 1, v_val_2681_);
                    if v_isShared_2684_ == 0 {
                        lean_ctor_set(v___x_2683_, 0, v___x_2688_);
                        v___x_2690_ = v___x_2683_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
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
    mut v_name_2707_: *mut LeanObject,
    mut v_e_2708_: *mut LeanObject,
    mut v_p_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2710_: *mut LeanObject = core::ptr::null_mut();
    v_res_2710_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_2707_, v_e_2708_, v_p_2709_);
    lean_dec(v_name_2707_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(
    mut v_goal_2711_: *mut LeanObject,
    mut v_name_2712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hyps_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    v_hyps_2713_ = lean_ctor_get(v_goal_2711_, 2);
    lean_inc_ref(v_hyps_2713_);
    lean_dec_ref(v_goal_2711_);
    v___x_2714_ = l_Lean_SubExpr_Pos_root;
    v___x_2715_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f_go(v_name_2712_, v_hyps_2713_, v___x_2714_);
    return v___x_2715_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f___boxed(
    mut v_goal_2716_: *mut LeanObject,
    mut v_name_2717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2718_: *mut LeanObject = core::ptr::null_mut();
    v_res_2718_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_findHyp_x3f(v_goal_2716_, v_name_2717_);
    lean_dec(v_name_2717_);
    return v_res_2718_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(
    mut v_msg_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
    mut v___y_2721_: *mut LeanObject,
    mut v___y_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2730_: u8 = 0;
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2725_ = lean_ctor_get(v___y_2722_, 5);
                v___x_2726_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v_msg_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
                v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
                v_isSharedCheck_2735_ = (!lean_is_exclusive(v___x_2726_)) as u8;
                if v_isSharedCheck_2735_ == 0 {
                    v___x_2729_ = v___x_2726_;
                    v_isShared_2730_ = v_isSharedCheck_2735_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2727_);
                    lean_dec(v___x_2726_);
                    v___x_2729_ = lean_box(0);
                    v_isShared_2730_ = v_isSharedCheck_2735_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2725_);
                v___x_2731_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2731_, 0, v_ref_2725_);
                lean_ctor_set(v___x_2731_, 1, v_a_2727_);
                if v_isShared_2730_ == 0 {
                    lean_ctor_set_tag(v___x_2729_, 1);
                    lean_ctor_set(v___x_2729_, 0, v___x_2731_);
                    v___x_2733_ = v___x_2729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
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
    mut v_msg_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2742_: *mut LeanObject = core::ptr::null_mut();
    v_res_2742_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(
            v_msg_2736_,
            v___y_2737_,
            v___y_2738_,
            v___y_2739_,
            v___y_2740_,
        );
    lean_dec(v___y_2740_);
    lean_dec_ref(v___y_2739_);
    lean_dec(v___y_2738_);
    lean_dec_ref(v___y_2737_);
    return v_res_2742_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(
    mut v___y_2750_: u8,
    mut v_suppressElabErrors_2751_: u8,
    mut v_x_2752_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_2752_) == 1 {
        let mut v_pre_2753_: *mut LeanObject = core::ptr::null_mut();
        v_pre_2753_ = lean_ctor_get(v_x_2752_, 0);
        match lean_obj_tag(v_pre_2753_) {
            1 => {
                let mut v_pre_2754_: *mut LeanObject = core::ptr::null_mut();
                v_pre_2754_ = lean_ctor_get(v_pre_2753_, 0);
                match lean_obj_tag(v_pre_2754_) {
                    0 => {
                        let mut v_str_2755_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_2756_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2758_: u8 = 0;
                        v_str_2755_ = lean_ctor_get(v_x_2752_, 1);
                        v_str_2756_ = lean_ctor_get(v_pre_2753_, 1);
                        v___x_2757_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__0;
                        v___x_2758_ = lean_string_dec_eq(v_str_2756_, v___x_2757_);
                        if v___x_2758_ == 0 {
                            let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2760_: u8 = 0;
                            v___x_2759_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f___closed__0;
                            v___x_2760_ = lean_string_dec_eq(v_str_2756_, v___x_2759_);
                            if v___x_2760_ == 0 {
                                return v___y_2750_;
                            } else {
                                let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_2765_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_2765_ = lean_ctor_get(v_pre_2754_, 0);
                        if lean_obj_tag(v_pre_2765_) == 0 {
                            let mut v_str_2766_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2767_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_2768_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2770_: u8 = 0;
                            v_str_2766_ = lean_ctor_get(v_x_2752_, 1);
                            v_str_2767_ = lean_ctor_get(v_pre_2753_, 1);
                            v_str_2768_ = lean_ctor_get(v_pre_2754_, 1);
                            v___x_2769_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__3;
                            v___x_2770_ = lean_string_dec_eq(v_str_2768_, v___x_2769_);
                            if v___x_2770_ == 0 {
                                return v___y_2750_;
                            } else {
                                let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_2772_: u8 = 0;
                                v___x_2771_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___closed__4;
                                v___x_2772_ = lean_string_dec_eq(v_str_2767_, v___x_2771_);
                                if v___x_2772_ == 0 {
                                    return v___y_2750_;
                                } else {
                                    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_2775_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2777_: u8 = 0;
                v_str_2775_ = lean_ctor_get(v_x_2752_, 1);
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
    mut v___y_2778_: *mut LeanObject,
    mut v_suppressElabErrors_2779_: *mut LeanObject,
    mut v_x_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4449__boxed_2781_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2782_: u8 = 0;
    let mut v_res_2783_: u8 = 0;
    let mut v_r_2784_: *mut LeanObject = core::ptr::null_mut();
    v___y_4449__boxed_2781_ = (lean_unbox(v___y_2778_) as u8);
    v_suppressElabErrors_boxed_2782_ = (lean_unbox(v_suppressElabErrors_2779_) as u8);
    v_res_2783_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0(v___y_4449__boxed_2781_, v_suppressElabErrors_boxed_2782_, v_x_2780_);
    lean_dec(v_x_2780_);
    v_r_2784_ = lean_box((v_res_2783_) as usize);
    return v_r_2784_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(
    mut v_opts_2785_: *mut LeanObject,
    mut v_opt_2786_: *mut LeanObject,
) -> u8 {
    let mut v_name_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    v_name_2787_ = lean_ctor_get(v_opt_2786_, 0);
    v_defValue_2788_ = lean_ctor_get(v_opt_2786_, 1);
    v_map_2789_ = lean_ctor_get(v_opts_2785_, 0);
    v___x_2790_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2789_,
            v_name_2787_,
        );
    if lean_obj_tag(v___x_2790_) == 0 {
        let mut v___x_2791_: u8 = 0;
        v___x_2791_ = (lean_unbox(v_defValue_2788_) as u8);
        return v___x_2791_;
    } else {
        let mut v_val_2792_: *mut LeanObject = core::ptr::null_mut();
        v_val_2792_ = lean_ctor_get(v___x_2790_, 0);
        lean_inc(v_val_2792_);
        lean_dec_ref_known(v___x_2790_, 1);
        if lean_obj_tag(v_val_2792_) == 1 {
            let mut v_v_2793_: u8 = 0;
            v_v_2793_ = lean_ctor_get_uint8(v_val_2792_, 0 as u32);
            lean_dec_ref_known(v_val_2792_, 0);
            return v_v_2793_;
        } else {
            let mut v___x_2794_: u8 = 0;
            lean_dec(v_val_2792_);
            v___x_2794_ = (lean_unbox(v_defValue_2788_) as u8);
            return v___x_2794_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_opts_2795_: *mut LeanObject,
    mut v_opt_2796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2797_: u8 = 0;
    let mut v_r_2798_: *mut LeanObject = core::ptr::null_mut();
    v_res_2797_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1_spec__3(v_opts_2795_, v_opt_2796_);
    lean_dec_ref(v_opt_2796_);
    lean_dec_ref(v_opts_2795_);
    v_r_2798_ = lean_box((v_res_2797_) as usize);
    return v_r_2798_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(
    mut v_ref_2800_: *mut LeanObject,
    mut v_msgData_2801_: *mut LeanObject,
    mut v_severity_2802_: u8,
    mut v_isSilent_2803_: u8,
    mut v___y_2804_: *mut LeanObject,
    mut v___y_2805_: *mut LeanObject,
    mut v___y_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: u8 = 0;
    let mut v___y_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: u8 = 0;
    let mut v___y_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2833_: u8 = 0;
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v___y_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2847_: u8 = 0;
    let mut v___y_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2849_: u8 = 0;
    let mut v___y_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2851_: u8 = 0;
    let mut v___y_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2859_: u8 = 0;
    let mut v___x_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: u8 = 0;
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2869_: u8 = 0;
    let mut v___y_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: u8 = 0;
    let mut v___y_2875_: u8 = 0;
    let mut v___y_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2877_: u8 = 0;
    let mut v___y_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2883_: u8 = 0;
    let mut v___y_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2885_: u8 = 0;
    let mut v___y_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: u8 = 0;
    let mut v_ref_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: u8 = 0;
    let mut v___y_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2897_: u8 = 0;
    let mut v___y_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2900_: u8 = 0;
    let mut v___y_2901_: u8 = 0;
    let mut v___y_2903_: u8 = 0;
    let mut v_fileName_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2908_: u8 = 0;
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_2801_);
                    v___x_2919_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2801_);
                    v___y_2903_ = v___x_2919_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2819_ = lean_st_ref_take(v___y_2818_);
                v_currNamespace_2820_ = lean_ctor_get(v___y_2817_, 6);
                v_openDecls_2821_ = lean_ctor_get(v___y_2817_, 7);
                v_env_2822_ = lean_ctor_get(v___x_2819_, 0);
                v_nextMacroScope_2823_ = lean_ctor_get(v___x_2819_, 1);
                v_ngen_2824_ = lean_ctor_get(v___x_2819_, 2);
                v_auxDeclNGen_2825_ = lean_ctor_get(v___x_2819_, 3);
                v_traceState_2826_ = lean_ctor_get(v___x_2819_, 4);
                v_cache_2827_ = lean_ctor_get(v___x_2819_, 5);
                v_messages_2828_ = lean_ctor_get(v___x_2819_, 6);
                v_infoState_2829_ = lean_ctor_get(v___x_2819_, 7);
                v_snapshotTasks_2830_ = lean_ctor_get(v___x_2819_, 8);
                v_isSharedCheck_2844_ = (!lean_is_exclusive(v___x_2819_)) as u8;
                if v_isSharedCheck_2844_ == 0 {
                    v___x_2832_ = v___x_2819_;
                    v_isShared_2833_ = v_isSharedCheck_2844_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2830_);
                    lean_inc(v_infoState_2829_);
                    lean_inc(v_messages_2828_);
                    lean_inc(v_cache_2827_);
                    lean_inc(v_traceState_2826_);
                    lean_inc(v_auxDeclNGen_2825_);
                    lean_inc(v_ngen_2824_);
                    lean_inc(v_nextMacroScope_2823_);
                    lean_inc(v_env_2822_);
                    lean_dec(v___x_2819_);
                    v___x_2832_ = lean_box(0);
                    v_isShared_2833_ = v_isSharedCheck_2844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_2821_);
                lean_inc(v_currNamespace_2820_);
                v___x_2834_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2834_, 0, v_currNamespace_2820_);
                lean_ctor_set(v___x_2834_, 1, v_openDecls_2821_);
                v___x_2835_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2835_, 0, v___x_2834_);
                lean_ctor_set(v___x_2835_, 1, v___y_2812_);
                lean_inc_ref(v___y_2811_);
                lean_inc_ref(v___y_2814_);
                v___x_2836_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_2836_, 0, v___y_2814_);
                lean_ctor_set(v___x_2836_, 1, v___y_2810_);
                lean_ctor_set(v___x_2836_, 2, v___y_2816_);
                lean_ctor_set(v___x_2836_, 3, v___y_2811_);
                lean_ctor_set(v___x_2836_, 4, v___x_2835_);
                lean_ctor_set_uint8(
                    v___x_2836_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_2813_,
                );
                lean_ctor_set_uint8(
                    v___x_2836_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_2815_,
                );
                lean_ctor_set_uint8(
                    v___x_2836_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2803_,
                );
                v___x_2837_ = l_Lean_MessageLog_add(v___x_2836_, v_messages_2828_);
                if v_isShared_2833_ == 0 {
                    lean_ctor_set(v___x_2832_, 6, v___x_2837_);
                    v___x_2839_ = v___x_2832_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_env_2822_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_nextMacroScope_2823_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_ngen_2824_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_auxDeclNGen_2825_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_traceState_2826_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 5, v_cache_2827_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 6, v___x_2837_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 7, v_infoState_2829_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 8, v_snapshotTasks_2830_);
                    v___x_2839_ = v_reuseFailAlloc_2843_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2840_ = lean_st_ref_set(v___y_2818_, v___x_2839_);
                v___x_2841_ = lean_box(0);
                v___x_2842_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2842_, 0, v___x_2841_);
                return v___x_2842_;
            }
            4 => {
                v___x_2854_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2801_,
                    );
                v___x_2855_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_ensureMGoal_spec__1_spec__1(v___x_2854_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
                v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
                v_isSharedCheck_2869_ = (!lean_is_exclusive(v___x_2855_)) as u8;
                if v_isSharedCheck_2869_ == 0 {
                    v___x_2858_ = v___x_2855_;
                    v_isShared_2859_ = v_isSharedCheck_2869_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_2856_);
                    lean_dec(v___x_2855_);
                    v___x_2858_ = lean_box(0);
                    v_isShared_2859_ = v_isSharedCheck_2869_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_2848_, 2);
                v___x_2860_ = l_Lean_FileMap_toPosition(v___y_2848_, v___y_2852_);
                lean_dec(v___y_2852_);
                v___x_2861_ = l_Lean_FileMap_toPosition(v___y_2848_, v___y_2853_);
                lean_dec(v___y_2853_);
                v___x_2862_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2862_, 0, v___x_2861_);
                v___x_2863_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___closed__0;
                if v___y_2847_ == 0 {
                    lean_del_object(v___x_2858_);
                    lean_dec_ref(v___y_2846_);
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
                    lean_inc(v_a_2856_);
                    v___x_2864_ = l_Lean_MessageData_hasTag(v___y_2846_, v_a_2856_);
                    if v___x_2864_ == 0 {
                        lean_dec_ref_known(v___x_2862_, 1);
                        lean_dec_ref(v___x_2860_);
                        lean_dec(v_a_2856_);
                        v___x_2865_ = lean_box(0);
                        if v_isShared_2859_ == 0 {
                            lean_ctor_set(v___x_2858_, 0, v___x_2865_);
                            v___x_2867_ = v___x_2858_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
                            v___x_2867_ = v_reuseFailAlloc_2868_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2858_);
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
                lean_dec(v___y_2872_);
                if lean_obj_tag(v___x_2879_) == 0 {
                    lean_inc(v___y_2878_);
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
                    v_val_2880_ = lean_ctor_get(v___x_2879_, 0);
                    lean_inc(v_val_2880_);
                    lean_dec_ref_known(v___x_2879_, 1);
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
                if lean_obj_tag(v___x_2890_) == 0 {
                    v___x_2891_ = lean_unsigned_to_nat(0);
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
                    v_val_2892_ = lean_ctor_get(v___x_2890_, 0);
                    lean_inc(v_val_2892_);
                    lean_dec_ref_known(v___x_2890_, 1);
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
                    v_fileName_2904_ = lean_ctor_get(v___y_2806_, 0);
                    v_fileMap_2905_ = lean_ctor_get(v___y_2806_, 1);
                    v_options_2906_ = lean_ctor_get(v___y_2806_, 2);
                    v_ref_2907_ = lean_ctor_get(v___y_2806_, 5);
                    v_suppressElabErrors_2908_ = lean_ctor_get_uint8(
                        v___y_2806_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2909_ = lean_box((v___y_2903_) as usize);
                    v___x_2910_ = lean_box((v_suppressElabErrors_2908_) as usize);
                    v___f_2911_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2911_, 0, v___x_2909_);
                    lean_closure_set(v___f_2911_, 1, v___x_2910_);
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
                    lean_dec_ref(v_msgData_2801_);
                    v___x_2916_ = lean_box(0);
                    v___x_2917_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2917_, 0, v___x_2916_);
                    return v___x_2917_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1___boxed(
    mut v_ref_2920_: *mut LeanObject,
    mut v_msgData_2921_: *mut LeanObject,
    mut v_severity_2922_: *mut LeanObject,
    mut v_isSilent_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
    mut v___y_2925_: *mut LeanObject,
    mut v___y_2926_: *mut LeanObject,
    mut v___y_2927_: *mut LeanObject,
    mut v___y_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2929_: u8 = 0;
    let mut v_isSilent_boxed_2930_: u8 = 0;
    let mut v_res_2931_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2929_ = (lean_unbox(v_severity_2922_) as u8);
    v_isSilent_boxed_2930_ = (lean_unbox(v_isSilent_2923_) as u8);
    v_res_2931_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_2920_, v_msgData_2921_, v_severity_boxed_2929_, v_isSilent_boxed_2930_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
    lean_dec(v___y_2927_);
    lean_dec_ref(v___y_2926_);
    lean_dec(v___y_2925_);
    lean_dec_ref(v___y_2924_);
    lean_dec(v_ref_2920_);
    return v_res_2931_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(
    mut v_msgData_2932_: *mut LeanObject,
    mut v_severity_2933_: u8,
    mut v_isSilent_2934_: u8,
    mut v___y_2935_: *mut LeanObject,
    mut v___y_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2940_ = lean_ctor_get(v___y_2937_, 5);
    v___x_2941_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0_spec__1(v_ref_2940_, v_msgData_2932_, v_severity_2933_, v_isSilent_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0___boxed(
    mut v_msgData_2942_: *mut LeanObject,
    mut v_severity_2943_: *mut LeanObject,
    mut v_isSilent_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_2950_: u8 = 0;
    let mut v_isSilent_boxed_2951_: u8 = 0;
    let mut v_res_2952_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_2950_ = (lean_unbox(v_severity_2943_) as u8);
    v_isSilent_boxed_2951_ = (lean_unbox(v_isSilent_2944_) as u8);
    v_res_2952_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_2942_, v_severity_boxed_2950_, v_isSilent_boxed_2951_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_);
    lean_dec(v___y_2948_);
    lean_dec_ref(v___y_2947_);
    lean_dec(v___y_2946_);
    lean_dec_ref(v___y_2945_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(
    mut v_msgData_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
    mut v___y_2955_: *mut LeanObject,
    mut v___y_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2959_: u8 = 0;
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = 1;
    v___x_2960_ = 0;
    v___x_2961_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0_spec__0(v_msgData_2953_, v___x_2959_, v___x_2960_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
    return v___x_2961_;
}
pub unsafe fn l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0___boxed(
    mut v_msgData_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
    mut v___y_2966_: *mut LeanObject,
    mut v___y_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2968_: *mut LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(
        v_msgData_2962_,
        v___y_2963_,
        v___y_2964_,
        v___y_2965_,
        v___y_2966_,
    );
    lean_dec(v___y_2966_);
    lean_dec_ref(v___y_2965_);
    lean_dec(v___y_2964_);
    lean_dec_ref(v___y_2963_);
    return v_res_2968_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1() -> *mut LeanObject {
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    v___x_2970_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__0;
    v___x_2971_ = l_Lean_stringToMessageData(v___x_2970_);
    return v___x_2971_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3() -> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    v___x_2973_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__2;
    v___x_2974_ = l_Lean_stringToMessageData(v___x_2973_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5() -> *mut LeanObject {
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    v___x_2976_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__4;
    v___x_2977_ = l_Lean_stringToMessageData(v___x_2976_);
    return v___x_2977_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7() -> *mut LeanObject {
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    v___x_2979_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__6;
    v___x_2980_ = l_Lean_stringToMessageData(v___x_2979_);
    return v___x_2980_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9() -> *mut LeanObject {
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    v___x_2982_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__8;
    v___x_2983_ = l_Lean_stringToMessageData(v___x_2982_);
    return v___x_2983_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(
    mut v_expr_2984_: *mut LeanObject,
    mut v_expectedType_2985_: *mut LeanObject,
    mut v_suppressWarning_2986_: u8,
    mut v_a_2987_: *mut LeanObject,
    mut v_a_2988_: *mut LeanObject,
    mut v_a_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: u8 = 0;
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: u8 = 0;
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut v_a_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3038_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3007_ = 0;
                lean_inc_ref(v_expr_2984_);
                v___x_3008_ = l_Lean_Meta_check(
                    v_expr_2984_,
                    v___x_3007_,
                    v_a_2987_,
                    v_a_2988_,
                    v_a_2989_,
                    v_a_2990_,
                );
                if lean_obj_tag(v___x_3008_) == 0 {
                    lean_dec_ref_known(v___x_3008_, 1);
                    lean_inc_ref(v_expectedType_2985_);
                    v___x_3009_ = l_Lean_Meta_check(
                        v_expectedType_2985_,
                        v___x_3007_,
                        v_a_2987_,
                        v_a_2988_,
                        v_a_2989_,
                        v_a_2990_,
                    );
                    if lean_obj_tag(v___x_3009_) == 0 {
                        lean_dec_ref_known(v___x_3009_, 1);
                        lean_inc(v_a_2990_);
                        lean_inc_ref(v_a_2989_);
                        lean_inc(v_a_2988_);
                        lean_inc_ref(v_a_2987_);
                        lean_inc_ref(v_expr_2984_);
                        v___x_3010_ = lean_infer_type(
                            v_expr_2984_,
                            v_a_2987_,
                            v_a_2988_,
                            v_a_2989_,
                            v_a_2990_,
                        );
                        if lean_obj_tag(v___x_3010_) == 0 {
                            v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
                            lean_inc_n(v_a_3011_, 2);
                            lean_dec_ref_known(v___x_3010_, 1);
                            lean_inc_ref(v_expectedType_2985_);
                            v___x_3012_ = l_Lean_Meta_isExprDefEqGuarded(
                                v_a_3011_,
                                v_expectedType_2985_,
                                v_a_2987_,
                                v_a_2988_,
                                v_a_2989_,
                                v_a_2990_,
                            );
                            if lean_obj_tag(v___x_3012_) == 0 {
                                v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
                                lean_inc(v_a_3013_);
                                lean_dec_ref_known(v___x_3012_, 1);
                                v___x_3014_ = (lean_unbox(v_a_3013_) as u8);
                                lean_dec(v_a_3013_);
                                if v___x_3014_ == 0 {
                                    v___x_3015_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__5);
                                    v___x_3016_ = l_Lean_indentExpr(v_expr_2984_);
                                    v___x_3017_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3017_, 0, v___x_3015_);
                                    lean_ctor_set(v___x_3017_, 1, v___x_3016_);
                                    v___x_3018_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__7);
                                    v___x_3019_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3019_, 0, v___x_3017_);
                                    lean_ctor_set(v___x_3019_, 1, v___x_3018_);
                                    v___x_3020_ = l_Lean_indentExpr(v_a_3011_);
                                    v___x_3021_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3021_, 0, v___x_3019_);
                                    lean_ctor_set(v___x_3021_, 1, v___x_3020_);
                                    v___x_3022_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__9);
                                    v___x_3023_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3023_, 0, v___x_3021_);
                                    lean_ctor_set(v___x_3023_, 1, v___x_3022_);
                                    v___x_3024_ = l_Lean_indentExpr(v_expectedType_2985_);
                                    v___x_3025_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_3025_, 0, v___x_3023_);
                                    lean_ctor_set(v___x_3025_, 1, v___x_3024_);
                                    v___x_3026_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_3025_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
                                    return v___x_3026_;
                                } else {
                                    lean_dec(v_a_3011_);
                                    v___y_2993_ = v_a_2987_;
                                    v___y_2994_ = v_a_2988_;
                                    v___y_2995_ = v_a_2989_;
                                    v___y_2996_ = v_a_2990_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3011_);
                                lean_dec_ref(v_expectedType_2985_);
                                lean_dec_ref(v_expr_2984_);
                                v_a_3027_ = lean_ctor_get(v___x_3012_, 0);
                                v_isSharedCheck_3034_ = (!lean_is_exclusive(v___x_3012_)) as u8;
                                if v_isSharedCheck_3034_ == 0 {
                                    v___x_3029_ = v___x_3012_;
                                    v_isShared_3030_ = v_isSharedCheck_3034_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3027_);
                                    lean_dec(v___x_3012_);
                                    v___x_3029_ = lean_box(0);
                                    v_isShared_3030_ = v_isSharedCheck_3034_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_expectedType_2985_);
                            lean_dec_ref(v_expr_2984_);
                            v_a_3035_ = lean_ctor_get(v___x_3010_, 0);
                            v_isSharedCheck_3042_ = (!lean_is_exclusive(v___x_3010_)) as u8;
                            if v_isSharedCheck_3042_ == 0 {
                                v___x_3037_ = v___x_3010_;
                                v_isShared_3038_ = v_isSharedCheck_3042_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3035_);
                                lean_dec(v___x_3010_);
                                v___x_3037_ = lean_box(0);
                                v_isShared_3038_ = v_isSharedCheck_3042_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_expectedType_2985_);
                        lean_dec_ref(v_expr_2984_);
                        return v___x_3009_;
                    }
                } else {
                    lean_dec_ref(v_expectedType_2985_);
                    lean_dec_ref(v_expr_2984_);
                    return v___x_3008_;
                }
            }
            1 => {
                if v_suppressWarning_2986_ == 0 {
                    v___x_2997_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__1,
                    );
                    v___x_2998_ = l_Lean_MessageData_ofExpr(v_expr_2984_);
                    v___x_2999_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2999_, 0, v___x_2997_);
                    lean_ctor_set(v___x_2999_, 1, v___x_2998_);
                    v___x_3000_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_checkHasType___closed__3,
                    );
                    v___x_3001_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3001_, 0, v___x_2999_);
                    lean_ctor_set(v___x_3001_, 1, v___x_3000_);
                    v___x_3002_ = l_Lean_MessageData_ofExpr(v_expectedType_2985_);
                    v___x_3003_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3003_, 0, v___x_3001_);
                    lean_ctor_set(v___x_3003_, 1, v___x_3002_);
                    v___x_3004_ = l_Lean_logWarning___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__0(v___x_3003_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
                    return v___x_3004_;
                } else {
                    lean_dec_ref(v_expectedType_2985_);
                    lean_dec_ref(v_expr_2984_);
                    v___x_3005_ = lean_box(0);
                    v___x_3006_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3006_, 0, v___x_3005_);
                    return v___x_3006_;
                }
            }
            2 => {
                if v_isShared_3030_ == 0 {
                    v___x_3032_ = v___x_3029_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
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
                    v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
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
    mut v_expr_3043_: *mut LeanObject,
    mut v_expectedType_3044_: *mut LeanObject,
    mut v_suppressWarning_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
    mut v_a_3048_: *mut LeanObject,
    mut v_a_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_suppressWarning_boxed_3051_: u8 = 0;
    let mut v_res_3052_: *mut LeanObject = core::ptr::null_mut();
    v_suppressWarning_boxed_3051_ = (lean_unbox(v_suppressWarning_3045_) as u8);
    v_res_3052_ = l_Lean_Elab_Tactic_Do_ProofMode_checkHasType(
        v_expr_3043_,
        v_expectedType_3044_,
        v_suppressWarning_boxed_3051_,
        v_a_3046_,
        v_a_3047_,
        v_a_3048_,
        v_a_3049_,
    );
    lean_dec(v_a_3049_);
    lean_dec_ref(v_a_3048_);
    lean_dec(v_a_3047_);
    lean_dec_ref(v_a_3046_);
    return v_res_3052_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(
    mut v_00_u03b1_3053_: *mut LeanObject,
    mut v_msg_3054_: *mut LeanObject,
    mut v___y_3055_: *mut LeanObject,
    mut v___y_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3061_: *mut LeanObject,
    mut v_msg_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
    mut v___y_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3068_: *mut LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1(
        v_00_u03b1_3061_,
        v_msg_3062_,
        v___y_3063_,
        v___y_3064_,
        v___y_3065_,
        v___y_3066_,
    );
    lean_dec(v___y_3066_);
    lean_dec_ref(v___y_3065_);
    lean_dec(v___y_3064_);
    lean_dec_ref(v___y_3063_);
    return v_res_3068_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(
    mut v_goal_3069_: *mut LeanObject,
    mut v_prf_3070_: *mut LeanObject,
    mut v_suppressWarning_3071_: u8,
    mut v_a_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
    mut v_a_3075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_goal_3079_: *mut LeanObject,
    mut v_prf_3080_: *mut LeanObject,
    mut v_suppressWarning_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_suppressWarning_boxed_3087_: u8 = 0;
    let mut v_res_3088_: *mut LeanObject = core::ptr::null_mut();
    v_suppressWarning_boxed_3087_ = (lean_unbox(v_suppressWarning_3081_) as u8);
    v_res_3088_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_checkProof(
        v_goal_3079_,
        v_prf_3080_,
        v_suppressWarning_boxed_3087_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
    );
    lean_dec(v_a_3085_);
    lean_dec_ref(v_a_3084_);
    lean_dec(v_a_3083_);
    lean_dec_ref(v_a_3082_);
    return v_res_3088_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(
    mut v_x_3100_: *mut LeanObject,
    mut v_a_3101_: *mut LeanObject,
    mut v_a_3102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: u8 = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3116_: u8 = 0;
    let mut v_a_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3120_: u8 = 0;
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3124_: u8 = 0;
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: u8 = 0;
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3139_: u8 = 0;
    let mut v_a_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3104_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__2;
                lean_inc(v_x_3100_);
                v___x_3105_ = l_Lean_Syntax_isOfKind(v_x_3100_, v___x_3104_);
                if v___x_3105_ == 0 {
                    v___x_3106_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4;
                    v___x_3107_ = l_Lean_Core_mkFreshUserName(v___x_3106_, v_a_3101_, v_a_3102_);
                    if lean_obj_tag(v___x_3107_) == 0 {
                        v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3116_ = (!lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3116_ == 0 {
                            v___x_3110_ = v___x_3107_;
                            v_isShared_3111_ = v_isSharedCheck_3116_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3108_);
                            lean_dec(v___x_3107_);
                            v___x_3110_ = lean_box(0);
                            v_isShared_3111_ = v_isSharedCheck_3116_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_x_3100_);
                        v_a_3117_ = lean_ctor_get(v___x_3107_, 0);
                        v_isSharedCheck_3124_ = (!lean_is_exclusive(v___x_3107_)) as u8;
                        if v_isSharedCheck_3124_ == 0 {
                            v___x_3119_ = v___x_3107_;
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3117_);
                            lean_dec(v___x_3107_);
                            v___x_3119_ = lean_box(0);
                            v_isShared_3120_ = v_isSharedCheck_3124_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_3125_ = lean_unsigned_to_nat(0);
                    v_name_3126_ = l_Lean_Syntax_getArg(v_x_3100_, v___x_3125_);
                    v___x_3127_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6;
                    lean_inc(v_name_3126_);
                    v___x_3128_ = l_Lean_Syntax_isOfKind(v_name_3126_, v___x_3127_);
                    if v___x_3128_ == 0 {
                        lean_dec(v_name_3126_);
                        v___x_3129_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__4;
                        v___x_3130_ =
                            l_Lean_Core_mkFreshUserName(v___x_3129_, v_a_3101_, v_a_3102_);
                        if lean_obj_tag(v___x_3130_) == 0 {
                            v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
                            v_isSharedCheck_3139_ = (!lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3139_ == 0 {
                                v___x_3133_ = v___x_3130_;
                                v_isShared_3134_ = v_isSharedCheck_3139_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3131_);
                                lean_dec(v___x_3130_);
                                v___x_3133_ = lean_box(0);
                                v_isShared_3134_ = v_isSharedCheck_3139_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_x_3100_);
                            v_a_3140_ = lean_ctor_get(v___x_3130_, 0);
                            v_isSharedCheck_3147_ = (!lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3147_ == 0 {
                                v___x_3142_ = v___x_3130_;
                                v_isShared_3143_ = v_isSharedCheck_3147_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_3140_);
                                lean_dec(v___x_3130_);
                                v___x_3142_ = lean_box(0);
                                v_isShared_3143_ = v_isSharedCheck_3147_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_x_3100_);
                        v___x_3148_ = l_Lean_TSyntax_getId(v_name_3126_);
                        v___x_3149_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3149_, 0, v___x_3148_);
                        lean_ctor_set(v___x_3149_, 1, v_name_3126_);
                        v___x_3150_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3150_, 0, v___x_3149_);
                        return v___x_3150_;
                    }
                }
            }
            1 => {
                v___x_3112_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3112_, 0, v_a_3108_);
                lean_ctor_set(v___x_3112_, 1, v_x_3100_);
                if v_isShared_3111_ == 0 {
                    lean_ctor_set(v___x_3110_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
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
                    v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
                    v___x_3122_ = v_reuseFailAlloc_3123_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3122_;
            }
            5 => {
                v___x_3135_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3135_, 0, v_a_3131_);
                lean_ctor_set(v___x_3135_, 1, v_x_3100_);
                if v_isShared_3134_ == 0 {
                    lean_ctor_set(v___x_3133_, 0, v___x_3135_);
                    v___x_3137_ = v___x_3133_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
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
                    v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
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
    mut v_x_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3155_: *mut LeanObject = core::ptr::null_mut();
    v_res_3155_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName(v_x_3151_, v_a_3152_, v_a_3153_);
    lean_dec(v_a_3153_);
    lean_dec_ref(v_a_3152_);
    return v_res_3155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(
    mut v_as_3156_: *mut LeanObject,
    mut v_i_3157_: usize,
    mut v_stop_3158_: usize,
    mut v_b_3159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3160_: u8 = 0;
    let mut v___x_3161_: usize = 0;
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3160_ = lean_usize_dec_eq(v_i_3157_, v_stop_3158_);
                if v___x_3160_ == 0 {
                    v___x_3161_ = 1usize;
                    v___x_3162_ = lean_usize_sub(v_i_3157_, v___x_3161_);
                    v___x_3163_ = lean_array_uget_borrowed(v_as_3156_, v___x_3162_);
                    v_snd_3164_ = lean_ctor_get(v___x_3163_, 1);
                    v_fst_3165_ = lean_ctor_get(v___x_3163_, 0);
                    v_fst_3166_ = lean_ctor_get(v_snd_3164_, 0);
                    v_snd_3167_ = lean_ctor_get(v_snd_3164_, 1);
                    v___x_3168_ = (lean_unbox(v_snd_3167_) as u8);
                    lean_inc(v_fst_3166_);
                    lean_inc(v_fst_3165_);
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
    mut v_as_3171_: *mut LeanObject,
    mut v_i_3172_: *mut LeanObject,
    mut v_stop_3173_: *mut LeanObject,
    mut v_b_3174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3175_: usize = 0;
    let mut v_stop_boxed_3176_: usize = 0;
    let mut v_res_3177_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3175_ = lean_unbox_usize(v_i_3172_);
    lean_dec(v_i_3172_);
    v_stop_boxed_3176_ = lean_unbox_usize(v_stop_3173_);
    lean_dec(v_stop_3173_);
    v_res_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_as_3171_, v_i_boxed_3175_, v_stop_boxed_3176_, v_b_3174_);
    lean_dec_ref(v_as_3171_);
    return v_res_3177_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(
    mut v_revLams_3178_: *mut LeanObject,
    mut v_revAppArgs_3179_: *mut LeanObject,
    mut v_body_3180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: u8 = 0;
    v___x_3181_ = 0;
    v___x_3182_ = l_Lean_Expr_betaRev(v_body_3180_, v_revAppArgs_3179_, v___x_3181_, v___x_3181_);
    v___x_3183_ = lean_array_get_size(v_revLams_3178_);
    v___x_3184_ = lean_unsigned_to_nat(0);
    v___x_3185_ = lean_nat_dec_lt(v___x_3184_, v___x_3183_);
    if v___x_3185_ == 0 {
        return v___x_3182_;
    } else {
        let mut v___x_3186_: usize = 0;
        let mut v___x_3187_: usize = 0;
        let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
        v___x_3186_ = lean_usize_of_nat(v___x_3183_);
        v___x_3187_ = 0usize;
        v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap_spec__0(v_revLams_3178_, v___x_3186_, v___x_3187_, v___x_3182_);
        return v___x_3188_;
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap___boxed(
    mut v_revLams_3189_: *mut LeanObject,
    mut v_revAppArgs_3190_: *mut LeanObject,
    mut v_body_3191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3192_: *mut LeanObject = core::ptr::null_mut();
    v_res_3192_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_3189_, v_revAppArgs_3190_, v_body_3191_);
    lean_dec_ref(v_revAppArgs_3190_);
    lean_dec_ref(v_revLams_3189_);
    return v_res_3192_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(
    mut v_00_u03c3s_3193_: *mut LeanObject,
    mut v_revLams_3194_: *mut LeanObject,
    mut v_revAppArgs_3195_: *mut LeanObject,
    mut v_e_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3228_: u8 = 0;
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3196_);
                v___x_3197_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_3196_);
                if lean_obj_tag(v___x_3197_) == 1 {
                    lean_dec_ref(v_e_3196_);
                    lean_dec_ref(v_revAppArgs_3195_);
                    lean_dec_ref(v_revLams_3194_);
                    v_val_3198_ = lean_ctor_get(v___x_3197_, 0);
                    lean_inc(v_val_3198_);
                    lean_dec_ref_known(v___x_3197_, 1);
                    v_fst_3199_ = lean_ctor_get(v_val_3198_, 0);
                    lean_inc(v_fst_3199_);
                    lean_dec(v_val_3198_);
                    v___x_3200_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_fst_3199_, v_00_u03c3s_3193_);
                    return v___x_3200_;
                } else {
                    lean_dec(v___x_3197_);
                    lean_inc_ref(v_e_3196_);
                    v___x_3201_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_3196_);
                    if lean_obj_tag(v___x_3201_) == 1 {
                        lean_dec_ref(v_e_3196_);
                        lean_dec_ref(v_00_u03c3s_3193_);
                        v_val_3202_ = lean_ctor_get(v___x_3201_, 0);
                        lean_inc(v_val_3202_);
                        lean_dec_ref_known(v___x_3201_, 1);
                        v_name_3203_ = lean_ctor_get(v_val_3202_, 0);
                        v_uniq_3204_ = lean_ctor_get(v_val_3202_, 1);
                        v_p_3205_ = lean_ctor_get(v_val_3202_, 2);
                        v_isSharedCheck_3214_ = (!lean_is_exclusive(v_val_3202_)) as u8;
                        if v_isSharedCheck_3214_ == 0 {
                            v___x_3207_ = v_val_3202_;
                            v_isShared_3208_ = v_isSharedCheck_3214_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_p_3205_);
                            lean_inc(v_uniq_3204_);
                            lean_inc(v_name_3203_);
                            lean_dec(v_val_3202_);
                            v___x_3207_ = lean_box(0);
                            v_isShared_3208_ = v_isSharedCheck_3214_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3201_);
                        v___x_3215_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_3196_);
                        if lean_obj_tag(v___x_3215_) == 1 {
                            lean_dec_ref(v_e_3196_);
                            v_val_3216_ = lean_ctor_get(v___x_3215_, 0);
                            lean_inc(v_val_3216_);
                            lean_dec_ref_known(v___x_3215_, 1);
                            v_snd_3217_ = lean_ctor_get(v_val_3216_, 1);
                            v_snd_3218_ = lean_ctor_get(v_snd_3217_, 1);
                            lean_inc(v_snd_3218_);
                            v_fst_3219_ = lean_ctor_get(v_val_3216_, 0);
                            lean_inc(v_fst_3219_);
                            lean_dec(v_val_3216_);
                            v_fst_3220_ = lean_ctor_get(v_snd_3218_, 0);
                            lean_inc(v_fst_3220_);
                            v_snd_3221_ = lean_ctor_get(v_snd_3218_, 1);
                            lean_inc(v_snd_3221_);
                            lean_dec(v_snd_3218_);
                            lean_inc_ref(v_revAppArgs_3195_);
                            lean_inc_ref(v_revLams_3194_);
                            lean_inc_ref_n(v_00_u03c3s_3193_, 2);
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
                            lean_dec(v___x_3215_);
                            if lean_obj_tag(v_e_3196_) == 6 {
                                v_binderName_3225_ = lean_ctor_get(v_e_3196_, 0);
                                lean_inc(v_binderName_3225_);
                                v_binderType_3226_ = lean_ctor_get(v_e_3196_, 1);
                                lean_inc_ref(v_binderType_3226_);
                                v_body_3227_ = lean_ctor_get(v_e_3196_, 2);
                                lean_inc_ref(v_body_3227_);
                                v_binderInfo_3228_ = lean_ctor_get_uint8(
                                    v_e_3196_,
                                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                                );
                                lean_dec_ref_known(v_e_3196_, 3);
                                v___x_3229_ = lean_array_get_size(v_revAppArgs_3195_);
                                v___x_3230_ = lean_unsigned_to_nat(1);
                                v___x_3231_ = lean_nat_sub(v___x_3229_, v___x_3230_);
                                v___x_3232_ = lean_nat_dec_lt(v___x_3231_, v___x_3229_);
                                if v___x_3232_ == 0 {
                                    lean_dec(v___x_3231_);
                                    v___x_3233_ = lean_box((v_binderInfo_3228_) as usize);
                                    v___x_3234_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3234_, 0, v_binderType_3226_);
                                    lean_ctor_set(v___x_3234_, 1, v___x_3233_);
                                    v___x_3235_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_3235_, 0, v_binderName_3225_);
                                    lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                                    v___x_3236_ = lean_array_push(v_revLams_3194_, v___x_3235_);
                                    v_revLams_3194_ = v___x_3236_;
                                    v_e_3196_ = v_body_3227_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_binderType_3226_);
                                    lean_dec(v_binderName_3225_);
                                    v___x_3238_ = lean_array_fget(v_revAppArgs_3195_, v___x_3231_);
                                    lean_dec(v___x_3231_);
                                    v___x_3239_ = lean_array_pop(v_revAppArgs_3195_);
                                    v___x_3240_ = lean_expr_instantiate1(v_body_3227_, v___x_3238_);
                                    lean_dec(v___x_3238_);
                                    lean_dec_ref(v_body_3227_);
                                    v_revAppArgs_3195_ = v___x_3239_;
                                    v_e_3196_ = v___x_3240_;
                                    state = 0;
                                    continue;
                                }
                            } else {
                                if lean_obj_tag(v_e_3196_) == 5 {
                                    v_fn_3242_ = lean_ctor_get(v_e_3196_, 0);
                                    lean_inc_ref(v_fn_3242_);
                                    v_arg_3243_ = lean_ctor_get(v_e_3196_, 1);
                                    lean_inc_ref(v_arg_3243_);
                                    lean_dec_ref_known(v_e_3196_, 2);
                                    v___x_3244_ = lean_array_push(v_revAppArgs_3195_, v_arg_3243_);
                                    v_revAppArgs_3195_ = v___x_3244_;
                                    v_e_3196_ = v_fn_3242_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_00_u03c3s_3193_);
                                    v___x_3246_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_3194_, v_revAppArgs_3195_, v_e_3196_);
                                    lean_dec_ref(v_revAppArgs_3195_);
                                    lean_dec_ref(v_revLams_3194_);
                                    return v___x_3246_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3209_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_wrap(v_revLams_3194_, v_revAppArgs_3195_, v_p_3205_);
                lean_dec_ref(v_revAppArgs_3195_);
                lean_dec_ref(v_revLams_3194_);
                if v_isShared_3208_ == 0 {
                    lean_ctor_set(v___x_3207_, 2, v___x_3209_);
                    v___x_3211_ = v___x_3207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_name_3203_);
                    lean_ctor_set(v_reuseFailAlloc_3213_, 1, v_uniq_3204_);
                    lean_ctor_set(v_reuseFailAlloc_3213_, 2, v___x_3209_);
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
    mut v_00_u03c3s_3249_: *mut LeanObject,
    mut v_hyps_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    v___x_3251_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps___closed__0;
    v___x_3252_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps_go(v_00_u03c3s_3249_, v___x_3251_, v___x_3251_, v_hyps_3250_);
    return v___x_3252_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(
    mut v_00_u03c3s_x27_3253_: *mut LeanObject,
    mut v_e_3254_: *mut LeanObject,
    mut v_args_3255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    v___x_3256_ = l_Lean_mkAppN(v_e_3254_, v_args_3255_);
    v___x_3257_ = l_Lean_Elab_Tactic_Do_ProofMode_pushForallContextIntoHyps(
        v_00_u03c3s_x27_3253_,
        v___x_3256_,
    );
    return v___x_3257_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames___boxed(
    mut v_00_u03c3s_x27_3258_: *mut LeanObject,
    mut v_e_3259_: *mut LeanObject,
    mut v_args_3260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3261_: *mut LeanObject = core::ptr::null_mut();
    v_res_3261_ = l_Lean_Elab_Tactic_Do_ProofMode_betaPreservingHypNames(
        v_00_u03c3s_x27_3258_,
        v_e_3259_,
        v_args_3260_,
    );
    lean_dec_ref(v_args_3260_);
    return v_res_3261_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__0;
    v___x_3264_ = l_Lean_stringToMessageData(v___x_3263_);
    return v___x_3264_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(
    mut v_upperBound_3265_: *mut LeanObject,
    mut v_a_3266_: *mut LeanObject,
    mut v_b_3267_: *mut LeanObject,
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
    mut v___y_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u8 = 0;
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: u8 = 0;
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3296_: u8 = 0;
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3278_ = lean_nat_dec_lt(v_a_3266_, v_upperBound_3265_);
                if v___x_3278_ == 0 {
                    lean_dec(v_a_3266_);
                    v___x_3279_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3279_, 0, v_b_3267_);
                    return v___x_3279_;
                } else {
                    lean_inc_ref(v_b_3267_);
                    v___x_3280_ = l_Lean_Meta_whnfR(
                        v_b_3267_,
                        v___y_3268_,
                        v___y_3269_,
                        v___y_3270_,
                        v___y_3271_,
                    );
                    if lean_obj_tag(v___x_3280_) == 0 {
                        v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
                        lean_inc(v_a_3281_);
                        lean_dec_ref_known(v___x_3280_, 1);
                        v___x_3282_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkCons___closed__1;
                        v___x_3283_ = lean_unsigned_to_nat(3);
                        v___x_3284_ = l_Lean_Expr_isAppOfArity(v_a_3281_, v___x_3282_, v___x_3283_);
                        if v___x_3284_ == 0 {
                            lean_dec(v_a_3281_);
                            v___x_3285_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg___closed__1);
                            lean_inc_ref(v_b_3267_);
                            v___x_3286_ = l_Lean_MessageData_ofExpr(v_b_3267_);
                            v___x_3287_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_3287_, 0, v___x_3285_);
                            lean_ctor_set(v___x_3287_, 1, v___x_3286_);
                            v___x_3288_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_3287_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
                            if lean_obj_tag(v___x_3288_) == 0 {
                                lean_dec_ref_known(v___x_3288_, 1);
                                v_a_3274_ = v_b_3267_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_b_3267_);
                                lean_dec(v_a_3266_);
                                v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
                                v_isSharedCheck_3296_ = (!lean_is_exclusive(v___x_3288_)) as u8;
                                if v_isSharedCheck_3296_ == 0 {
                                    v___x_3291_ = v___x_3288_;
                                    v_isShared_3292_ = v_isSharedCheck_3296_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3289_);
                                    lean_dec(v___x_3288_);
                                    v___x_3291_ = lean_box(0);
                                    v_isShared_3292_ = v_isSharedCheck_3296_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_b_3267_);
                            v___x_3297_ = l_Lean_Expr_appArg_x21(v_a_3281_);
                            lean_dec(v_a_3281_);
                            v_a_3274_ = v___x_3297_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_b_3267_);
                        lean_dec(v_a_3266_);
                        return v___x_3280_;
                    }
                }
            }
            1 => {
                v___x_3275_ = lean_unsigned_to_nat(1);
                v___x_3276_ = lean_nat_add(v_a_3266_, v___x_3275_);
                lean_dec(v_a_3266_);
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
                    v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
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
    mut v_upperBound_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
    mut v_b_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
    mut v___y_3302_: *mut LeanObject,
    mut v___y_3303_: *mut LeanObject,
    mut v___y_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3306_: *mut LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_3298_, v_a_3299_, v_b_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
    lean_dec(v___y_3304_);
    lean_dec_ref(v___y_3303_);
    lean_dec(v___y_3302_);
    lean_dec_ref(v___y_3301_);
    lean_dec(v_upperBound_3298_);
    return v_res_3306_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(
    mut v_00_u03c3s_3307_: *mut LeanObject,
    mut v_n_3308_: *mut LeanObject,
    mut v_a_3309_: *mut LeanObject,
    mut v_a_3310_: *mut LeanObject,
    mut v_a_3311_: *mut LeanObject,
    mut v_a_3312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ = lean_unsigned_to_nat(0);
    v___x_3315_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_n_3308_, v___x_3314_, v_00_u03c3s_3307_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
    return v___x_3315_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_dropStateList___boxed(
    mut v_00_u03c3s_3316_: *mut LeanObject,
    mut v_n_3317_: *mut LeanObject,
    mut v_a_3318_: *mut LeanObject,
    mut v_a_3319_: *mut LeanObject,
    mut v_a_3320_: *mut LeanObject,
    mut v_a_3321_: *mut LeanObject,
    mut v_a_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3323_: *mut LeanObject = core::ptr::null_mut();
    v_res_3323_ = l_Lean_Elab_Tactic_Do_ProofMode_dropStateList(
        v_00_u03c3s_3316_,
        v_n_3317_,
        v_a_3318_,
        v_a_3319_,
        v_a_3320_,
        v_a_3321_,
    );
    lean_dec(v_a_3321_);
    lean_dec_ref(v_a_3320_);
    lean_dec(v_a_3319_);
    lean_dec_ref(v_a_3318_);
    lean_dec(v_n_3317_);
    return v_res_3323_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0(
    mut v_upperBound_3324_: *mut LeanObject,
    mut v_inst_3325_: *mut LeanObject,
    mut v_R_3326_: *mut LeanObject,
    mut v_a_3327_: *mut LeanObject,
    mut v_b_3328_: *mut LeanObject,
    mut v_c_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    v___x_3335_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___redArg(v_upperBound_3324_, v_a_3327_, v_b_3328_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
    return v___x_3335_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_Do_ProofMode_dropStateList_spec__0___boxed(
    mut v_upperBound_3336_: *mut LeanObject,
    mut v_inst_3337_: *mut LeanObject,
    mut v_R_3338_: *mut LeanObject,
    mut v_a_3339_: *mut LeanObject,
    mut v_b_3340_: *mut LeanObject,
    mut v_c_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3347_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3345_);
    lean_dec_ref(v___y_3344_);
    lean_dec(v___y_3343_);
    lean_dec_ref(v___y_3342_);
    lean_dec(v_upperBound_3336_);
    return v_res_3347_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(
    mut v_H_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: u8 = 0;
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3359_: u8 = 0;
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3364_: u8 = 0;
    let mut v_unused_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3369_: u8 = 0;
    let mut v_val_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v_name_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v_idents_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: u8 = 0;
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: u8 = 0;
    let mut v___x_3412_: u8 = 0;
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut v_isSharedCheck_3415_: u8 = 0;
    let mut v_unused_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v_fst_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3439_: u8 = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut v_isSharedCheck_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3351_ = lean_ctor_get(v_a_3349_, 0);
                v_snd_3352_ = lean_ctor_get(v_a_3349_, 1);
                v___x_3353_ = lean_array_get_size(v_snd_3352_);
                v___x_3354_ = lean_unsigned_to_nat(0);
                v___x_3355_ = lean_nat_dec_eq(v___x_3353_, v___x_3354_);
                if v___x_3355_ == 0 {
                    lean_inc_ref(v_H_3348_);
                    v___x_3356_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_H_3348_);
                    if lean_obj_tag(v___x_3356_) == 1 {
                        v_isSharedCheck_3364_ = (!lean_is_exclusive(v___x_3356_)) as u8;
                        if v_isSharedCheck_3364_ == 0 {
                            v_unused_3365_ = lean_ctor_get(v___x_3356_, 0);
                            lean_dec(v_unused_3365_);
                            v___x_3358_ = v___x_3356_;
                            v_isShared_3359_ = v_isSharedCheck_3364_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3356_);
                            v___x_3358_ = lean_box(0);
                            v_isShared_3359_ = v_isSharedCheck_3364_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3356_);
                        lean_inc_ref(v_H_3348_);
                        v___x_3366_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_H_3348_);
                        if lean_obj_tag(v___x_3366_) == 1 {
                            lean_inc(v_snd_3352_);
                            lean_inc(v_fst_3351_);
                            v_isSharedCheck_3415_ = (!lean_is_exclusive(v_a_3349_)) as u8;
                            if v_isSharedCheck_3415_ == 0 {
                                v_unused_3416_ = lean_ctor_get(v_a_3349_, 1);
                                lean_dec(v_unused_3416_);
                                v_unused_3417_ = lean_ctor_get(v_a_3349_, 0);
                                lean_dec(v_unused_3417_);
                                v___x_3368_ = v_a_3349_;
                                v_isShared_3369_ = v_isSharedCheck_3415_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v_a_3349_);
                                v___x_3368_ = lean_box(0);
                                v_isShared_3369_ = v_isSharedCheck_3415_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3366_);
                            v___x_3418_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_H_3348_);
                            if lean_obj_tag(v___x_3418_) == 1 {
                                lean_dec_ref(v_H_3348_);
                                v_val_3419_ = lean_ctor_get(v___x_3418_, 0);
                                lean_inc(v_val_3419_);
                                lean_dec_ref_known(v___x_3418_, 1);
                                v_snd_3420_ = lean_ctor_get(v_val_3419_, 1);
                                lean_inc(v_snd_3420_);
                                v_snd_3421_ = lean_ctor_get(v_snd_3420_, 1);
                                lean_inc(v_snd_3421_);
                                v_fst_3422_ = lean_ctor_get(v_val_3419_, 0);
                                lean_inc(v_fst_3422_);
                                lean_dec(v_val_3419_);
                                v_fst_3423_ = lean_ctor_get(v_snd_3420_, 0);
                                lean_inc(v_fst_3423_);
                                lean_dec(v_snd_3420_);
                                v_fst_3424_ = lean_ctor_get(v_snd_3421_, 0);
                                lean_inc(v_fst_3424_);
                                v_snd_3425_ = lean_ctor_get(v_snd_3421_, 1);
                                lean_inc(v_snd_3425_);
                                lean_dec(v_snd_3421_);
                                v___x_3426_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_snd_3425_, v_a_3349_);
                                if lean_obj_tag(v___x_3426_) == 0 {
                                    v_a_3427_ = lean_ctor_get(v___x_3426_, 0);
                                    lean_inc(v_a_3427_);
                                    lean_dec_ref_known(v___x_3426_, 1);
                                    v_fst_3428_ = lean_ctor_get(v_a_3427_, 0);
                                    lean_inc(v_fst_3428_);
                                    v_snd_3429_ = lean_ctor_get(v_a_3427_, 1);
                                    lean_inc(v_snd_3429_);
                                    lean_dec(v_a_3427_);
                                    v___x_3430_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_fst_3424_, v_snd_3429_);
                                    if lean_obj_tag(v___x_3430_) == 0 {
                                        v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
                                        v_isSharedCheck_3448_ =
                                            (!lean_is_exclusive(v___x_3430_)) as u8;
                                        if v_isSharedCheck_3448_ == 0 {
                                            v___x_3433_ = v___x_3430_;
                                            v_isShared_3434_ = v_isSharedCheck_3448_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3431_);
                                            lean_dec(v___x_3430_);
                                            v___x_3433_ = lean_box(0);
                                            v_isShared_3434_ = v_isSharedCheck_3448_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_fst_3428_);
                                        lean_dec(v_fst_3423_);
                                        lean_dec(v_fst_3422_);
                                        return v___x_3430_;
                                    }
                                } else {
                                    lean_dec(v_fst_3424_);
                                    lean_dec(v_fst_3423_);
                                    lean_dec(v_fst_3422_);
                                    return v___x_3426_;
                                }
                            } else {
                                lean_dec(v___x_3418_);
                                v___x_3449_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3449_, 0, v_H_3348_);
                                lean_ctor_set(v___x_3449_, 1, v_a_3349_);
                                v___x_3450_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3450_, 0, v___x_3449_);
                                return v___x_3450_;
                            }
                        }
                    }
                } else {
                    v___x_3451_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3451_, 0, v_H_3348_);
                    lean_ctor_set(v___x_3451_, 1, v_a_3349_);
                    v___x_3452_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3452_, 0, v___x_3451_);
                    return v___x_3452_;
                }
            }
            1 => {
                v___x_3360_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3360_, 0, v_H_3348_);
                lean_ctor_set(v___x_3360_, 1, v_a_3349_);
                if v_isShared_3359_ == 0 {
                    lean_ctor_set_tag(v___x_3358_, 0);
                    lean_ctor_set(v___x_3358_, 0, v___x_3360_);
                    v___x_3362_ = v___x_3358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
                    v___x_3362_ = v_reuseFailAlloc_3363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3362_;
            }
            3 => {
                v_val_3370_ = lean_ctor_get(v___x_3366_, 0);
                v_isSharedCheck_3414_ = (!lean_is_exclusive(v___x_3366_)) as u8;
                if v_isSharedCheck_3414_ == 0 {
                    v___x_3372_ = v___x_3366_;
                    v_isShared_3373_ = v_isSharedCheck_3414_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_val_3370_);
                    lean_dec(v___x_3366_);
                    v___x_3372_ = lean_box(0);
                    v_isShared_3373_ = v_isSharedCheck_3414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_name_3374_ = lean_ctor_get(v_val_3370_, 0);
                v_uniq_3375_ = lean_ctor_get(v_val_3370_, 1);
                v_p_3376_ = lean_ctor_get(v_val_3370_, 2);
                v_isSharedCheck_3413_ = (!lean_is_exclusive(v_val_3370_)) as u8;
                if v_isSharedCheck_3413_ == 0 {
                    v___x_3378_ = v_val_3370_;
                    v_isShared_3379_ = v_isSharedCheck_3413_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_p_3376_);
                    lean_inc(v_uniq_3375_);
                    lean_inc(v_name_3374_);
                    lean_dec(v_val_3370_);
                    v___x_3378_ = lean_box(0);
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
                        lean_del_object(v___x_3378_);
                        lean_dec_ref(v_p_3376_);
                        lean_dec(v_uniq_3375_);
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
                    lean_ctor_set(v___x_3368_, 1, v_idents_3381_);
                    lean_ctor_set(v___x_3368_, 0, v___x_3382_);
                    v___x_3384_ = v___x_3368_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3382_);
                    lean_ctor_set(v_reuseFailAlloc_3389_, 1, v_idents_3381_);
                    v___x_3384_ = v_reuseFailAlloc_3389_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3385_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3385_, 0, v_H_3348_);
                lean_ctor_set(v___x_3385_, 1, v___x_3384_);
                if v_isShared_3373_ == 0 {
                    lean_ctor_set_tag(v___x_3372_, 0);
                    lean_ctor_set(v___x_3372_, 0, v___x_3385_);
                    v___x_3387_ = v___x_3372_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
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
                v___x_3392_ = lean_box(0);
                v___x_3393_ = lean_unsigned_to_nat(1);
                v___x_3394_ = lean_nat_sub(v___x_3353_, v___x_3393_);
                v___x_3395_ = lean_array_get_borrowed(v___x_3392_, v_snd_3352_, v___x_3394_);
                lean_dec(v___x_3394_);
                lean_inc(v___x_3395_);
                v___x_3396_ = l_Lean_Syntax_isOfKind(v___x_3395_, v___x_3391_);
                if v___x_3396_ == 0 {
                    lean_del_object(v___x_3378_);
                    lean_dec_ref(v_p_3376_);
                    lean_dec(v_uniq_3375_);
                    v___x_3397_ = lean_array_pop(v_snd_3352_);
                    v_idents_3381_ = v___x_3397_;
                    state = 6;
                    continue;
                } else {
                    v___x_3398_ = l_Lean_Syntax_getArg(v___x_3395_, v___x_3354_);
                    v___x_3399_ = l_Lean_Elab_Tactic_Do_ProofMode_getFreshHypName___closed__6;
                    lean_inc(v___x_3398_);
                    v___x_3400_ = l_Lean_Syntax_isOfKind(v___x_3398_, v___x_3399_);
                    if v___x_3400_ == 0 {
                        lean_dec(v___x_3398_);
                        lean_del_object(v___x_3378_);
                        lean_dec_ref(v_p_3376_);
                        lean_dec(v_uniq_3375_);
                        v___x_3401_ = lean_array_pop(v_snd_3352_);
                        v_idents_3381_ = v___x_3401_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_name_3374_);
                        lean_del_object(v___x_3372_);
                        lean_del_object(v___x_3368_);
                        lean_dec_ref(v_H_3348_);
                        v___x_3402_ = l_Lean_TSyntax_getId(v___x_3398_);
                        lean_dec(v___x_3398_);
                        if v_isShared_3379_ == 0 {
                            lean_ctor_set(v___x_3378_, 0, v___x_3402_);
                            v___x_3404_ = v___x_3378_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3402_);
                            lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_uniq_3375_);
                            lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_p_3376_);
                            v___x_3404_ = v_reuseFailAlloc_3410_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            10 => {
                v___x_3405_ = lean_array_pop(v_snd_3352_);
                v___x_3406_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3406_, 0, v_fst_3351_);
                lean_ctor_set(v___x_3406_, 1, v___x_3405_);
                v___x_3407_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_3404_);
                v___x_3408_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3408_, 0, v___x_3407_);
                lean_ctor_set(v___x_3408_, 1, v___x_3406_);
                v___x_3409_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3409_, 0, v___x_3408_);
                return v___x_3409_;
            }
            11 => {
                v_fst_3435_ = lean_ctor_get(v_a_3431_, 0);
                v_snd_3436_ = lean_ctor_get(v_a_3431_, 1);
                v_isSharedCheck_3447_ = (!lean_is_exclusive(v_a_3431_)) as u8;
                if v_isSharedCheck_3447_ == 0 {
                    v___x_3438_ = v_a_3431_;
                    v_isShared_3439_ = v_isSharedCheck_3447_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_snd_3436_);
                    lean_inc(v_fst_3435_);
                    lean_dec(v_a_3431_);
                    v___x_3438_ = lean_box(0);
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
                    lean_ctor_set(v___x_3438_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3438_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3440_);
                    lean_ctor_set(v_reuseFailAlloc_3446_, 1, v_snd_3436_);
                    v___x_3442_ = v_reuseFailAlloc_3446_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3434_ == 0 {
                    lean_ctor_set(v___x_3433_, 0, v___x_3442_);
                    v___x_3444_ = v___x_3433_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
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
    mut v_H_3453_: *mut LeanObject,
    mut v_a_3454_: *mut LeanObject,
    mut v_a_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3456_: *mut LeanObject = core::ptr::null_mut();
    v_res_3456_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_3453_, v_a_3454_);
    return v_res_3456_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(
    mut v_H_3457_: *mut LeanObject,
    mut v_a_3458_: *mut LeanObject,
    mut v_a_3459_: *mut LeanObject,
    mut v_a_3460_: *mut LeanObject,
    mut v_a_3461_: *mut LeanObject,
    mut v_a_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    v___x_3464_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_H_3457_, v_a_3458_);
    return v___x_3464_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___boxed(
    mut v_H_3465_: *mut LeanObject,
    mut v_a_3466_: *mut LeanObject,
    mut v_a_3467_: *mut LeanObject,
    mut v_a_3468_: *mut LeanObject,
    mut v_a_3469_: *mut LeanObject,
    mut v_a_3470_: *mut LeanObject,
    mut v_a_3471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3472_: *mut LeanObject = core::ptr::null_mut();
    v_res_3472_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go(v_H_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_);
    lean_dec(v_a_3470_);
    lean_dec_ref(v_a_3469_);
    lean_dec(v_a_3468_);
    lean_dec_ref(v_a_3467_);
    return v_res_3472_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(
    mut v_a_3473_: *mut LeanObject,
    mut v_a_3474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3473_) == 0 {
                    v___x_3475_ = l_List_reverse___redArg(v_a_3474_);
                    return v___x_3475_;
                } else {
                    v_head_3476_ = lean_ctor_get(v_a_3473_, 0);
                    v_tail_3477_ = lean_ctor_get(v_a_3473_, 1);
                    v_isSharedCheck_3486_ = (!lean_is_exclusive(v_a_3473_)) as u8;
                    if v_isSharedCheck_3486_ == 0 {
                        v___x_3479_ = v_a_3473_;
                        v_isShared_3480_ = v_isSharedCheck_3486_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3477_);
                        lean_inc(v_head_3476_);
                        lean_dec(v_a_3473_);
                        v___x_3479_ = lean_box(0);
                        v_isShared_3480_ = v_isSharedCheck_3486_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3481_ = l_Lean_MessageData_ofSyntax(v_head_3476_);
                if v_isShared_3480_ == 0 {
                    lean_ctor_set(v___x_3479_, 1, v_a_3474_);
                    lean_ctor_set(v___x_3479_, 0, v___x_3481_);
                    v___x_3483_ = v___x_3479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3481_);
                    lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_a_3474_);
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
-> *mut LeanObject {
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    v___x_3488_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__0;
    v___x_3489_ = l_Lean_stringToMessageData(v___x_3488_);
    return v___x_3489_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3()
-> *mut LeanObject {
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    v___x_3491_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__2;
    v___x_3492_ = l_Lean_stringToMessageData(v___x_3491_);
    return v___x_3492_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(
    mut v_goal_3493_: *mut LeanObject,
    mut v_idents_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3510_: u8 = 0;
    let mut v_fst_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3515_: u8 = 0;
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3545_: u8 = 0;
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_reuseFailAlloc_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3552_: u8 = 0;
    let mut v_unused_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3554_: u8 = 0;
    let mut v_isSharedCheck_3555_: u8 = 0;
    let mut v_a_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3559_: u8 = 0;
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_3500_ = lean_ctor_get(v_goal_3493_, 0);
                v_00_u03c3s_3501_ = lean_ctor_get(v_goal_3493_, 1);
                v_hyps_3502_ = lean_ctor_get(v_goal_3493_, 2);
                v_target_3503_ = lean_ctor_get(v_goal_3493_, 3);
                v___x_3504_ = l_Lean_NameSet_empty;
                v___x_3505_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3505_, 0, v___x_3504_);
                lean_ctor_set(v___x_3505_, 1, v_idents_3494_);
                lean_inc_ref(v_hyps_3502_);
                v___x_3506_ = l___private_Lean_Elab_Tactic_Do_ProofMode_MGoal_0__Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_go___redArg(v_hyps_3502_, v___x_3505_);
                if lean_obj_tag(v___x_3506_) == 0 {
                    v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3555_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3555_ == 0 {
                        v___x_3509_ = v___x_3506_;
                        v_isShared_3510_ = v_isSharedCheck_3555_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3507_);
                        lean_dec(v___x_3506_);
                        v___x_3509_ = lean_box(0);
                        v_isShared_3510_ = v_isSharedCheck_3555_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_goal_3493_);
                    v_a_3556_ = lean_ctor_get(v___x_3506_, 0);
                    v_isSharedCheck_3563_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                    if v_isSharedCheck_3563_ == 0 {
                        v___x_3558_ = v___x_3506_;
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3556_);
                        lean_dec(v___x_3506_);
                        v___x_3558_ = lean_box(0);
                        v_isShared_3559_ = v_isSharedCheck_3563_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3511_ = lean_ctor_get(v_a_3507_, 0);
                v_snd_3512_ = lean_ctor_get(v_a_3507_, 1);
                v_isSharedCheck_3554_ = (!lean_is_exclusive(v_a_3507_)) as u8;
                if v_isSharedCheck_3554_ == 0 {
                    v___x_3514_ = v_a_3507_;
                    v_isShared_3515_ = v_isSharedCheck_3554_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_3512_);
                    lean_inc(v_fst_3511_);
                    lean_dec(v_a_3507_);
                    v___x_3514_ = lean_box(0);
                    v_isShared_3515_ = v_isSharedCheck_3554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_snd_3521_ = lean_ctor_get(v_snd_3512_, 1);
                v_isSharedCheck_3552_ = (!lean_is_exclusive(v_snd_3512_)) as u8;
                if v_isSharedCheck_3552_ == 0 {
                    v_unused_3553_ = lean_ctor_get(v_snd_3512_, 0);
                    lean_dec(v_unused_3553_);
                    v___x_3523_ = v_snd_3512_;
                    v_isShared_3524_ = v_isSharedCheck_3552_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_3521_);
                    lean_dec(v_snd_3512_);
                    v___x_3523_ = lean_box(0);
                    v_isShared_3524_ = v_isSharedCheck_3552_;
                    state = 5;
                    continue;
                }
            }
            3 => {
                v___x_3517_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3517_, 0, v_u_3500_);
                lean_ctor_set(v___x_3517_, 1, v_00_u03c3s_3501_);
                lean_ctor_set(v___x_3517_, 2, v_fst_3511_);
                lean_ctor_set(v___x_3517_, 3, v_target_3503_);
                if v_isShared_3510_ == 0 {
                    lean_ctor_set(v___x_3509_, 0, v___x_3517_);
                    v___x_3519_ = v___x_3509_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3517_);
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
                v___x_3526_ = lean_unsigned_to_nat(0);
                v___x_3527_ = lean_nat_dec_eq(v___x_3525_, v___x_3526_);
                if v___x_3527_ == 0 {
                    lean_dec(v_fst_3511_);
                    lean_del_object(v___x_3509_);
                    v___x_3528_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__1);
                    v___x_3529_ = lean_array_to_list(v_snd_3521_);
                    v___x_3530_ = lean_box(0);
                    v___x_3531_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps_spec__0(v___x_3529_, v___x_3530_);
                    v___x_3532_ = l_Lean_MessageData_ofList(v___x_3531_);
                    if v_isShared_3524_ == 0 {
                        lean_ctor_set_tag(v___x_3523_, 7);
                        lean_ctor_set(v___x_3523_, 1, v___x_3532_);
                        lean_ctor_set(v___x_3523_, 0, v___x_3528_);
                        v___x_3534_ = v___x_3523_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3551_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 0, v___x_3528_);
                        lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3532_);
                        v___x_3534_ = v_reuseFailAlloc_3551_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_target_3503_);
                    lean_inc_ref(v_00_u03c3s_3501_);
                    lean_inc(v_u_3500_);
                    lean_del_object(v___x_3523_);
                    lean_dec(v_snd_3521_);
                    lean_del_object(v___x_3514_);
                    lean_dec_ref(v_goal_3493_);
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_3535_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps___closed__3);
                if v_isShared_3515_ == 0 {
                    lean_ctor_set_tag(v___x_3514_, 7);
                    lean_ctor_set(v___x_3514_, 1, v___x_3535_);
                    lean_ctor_set(v___x_3514_, 0, v___x_3534_);
                    v___x_3537_ = v___x_3514_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3550_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3534_);
                    lean_ctor_set(v_reuseFailAlloc_3550_, 1, v___x_3535_);
                    v___x_3537_ = v_reuseFailAlloc_3550_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3538_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_3493_);
                v___x_3539_ = l_Lean_MessageData_ofExpr(v___x_3538_);
                v___x_3540_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3540_, 0, v___x_3537_);
                lean_ctor_set(v___x_3540_, 1, v___x_3539_);
                v___x_3541_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_checkHasType_spec__1___redArg(v___x_3540_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
                v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
                v_isSharedCheck_3549_ = (!lean_is_exclusive(v___x_3541_)) as u8;
                if v_isSharedCheck_3549_ == 0 {
                    v___x_3544_ = v___x_3541_;
                    v_isShared_3545_ = v_isSharedCheck_3549_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_a_3542_);
                    lean_dec(v___x_3541_);
                    v___x_3544_ = lean_box(0);
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
                    v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
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
                    v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
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
    mut v_goal_3564_: *mut LeanObject,
    mut v_idents_3565_: *mut LeanObject,
    mut v_a_3566_: *mut LeanObject,
    mut v_a_3567_: *mut LeanObject,
    mut v_a_3568_: *mut LeanObject,
    mut v_a_3569_: *mut LeanObject,
    mut v_a_3570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3571_: *mut LeanObject = core::ptr::null_mut();
    v_res_3571_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_renameInaccessibleHyps(
        v_goal_3564_,
        v_idents_3565_,
        v_a_3566_,
        v_a_3567_,
        v_a_3568_,
        v_a_3569_,
    );
    lean_dec(v_a_3569_);
    lean_dec_ref(v_a_3568_);
    lean_dec(v_a_3567_);
    lean_dec_ref(v_a_3566_);
    return v_res_3571_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0(
    mut v_stx_3572_: *mut LeanObject,
    mut v_lctx_3573_: *mut LeanObject,
    mut v_expectedType_x3f_3574_: *mut LeanObject,
    mut v_expr_3575_: *mut LeanObject,
    mut v_isBinder_3576_: u8,
    mut v_x_3577_: *mut LeanObject,
    mut v___y_3578_: *mut LeanObject,
    mut v___y_3579_: *mut LeanObject,
    mut v___y_3580_: *mut LeanObject,
    mut v___y_3581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: u8 = 0;
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    v___x_3583_ = lean_box(0);
    v___x_3584_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3584_, 0, v___x_3583_);
    lean_ctor_set(v___x_3584_, 1, v_stx_3572_);
    v___x_3585_ = 0;
    v___x_3586_ = lean_alloc_ctor(0, 4, (2) as u32);
    lean_ctor_set(v___x_3586_, 0, v___x_3584_);
    lean_ctor_set(v___x_3586_, 1, v_lctx_3573_);
    lean_ctor_set(v___x_3586_, 2, v_expectedType_x3f_3574_);
    lean_ctor_set(v___x_3586_, 3, v_expr_3575_);
    lean_ctor_set_uint8(
        v___x_3586_,
        (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
        v_isBinder_3576_,
    );
    lean_ctor_set_uint8(
        v___x_3586_,
        (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
        v___x_3585_,
    );
    v___x_3587_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3587_, 0, v___x_3586_);
    v___x_3588_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3588_, 0, v___x_3587_);
    v___x_3589_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3589_, 0, v___x_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed(
    mut v_stx_3590_: *mut LeanObject,
    mut v_lctx_3591_: *mut LeanObject,
    mut v_expectedType_x3f_3592_: *mut LeanObject,
    mut v_expr_3593_: *mut LeanObject,
    mut v_isBinder_3594_: *mut LeanObject,
    mut v_x_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
    mut v___y_3598_: *mut LeanObject,
    mut v___y_3599_: *mut LeanObject,
    mut v___y_3600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isBinder_boxed_3601_: u8 = 0;
    let mut v_res_3602_: *mut LeanObject = core::ptr::null_mut();
    v_isBinder_boxed_3601_ = (lean_unbox(v_isBinder_3594_) as u8);
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
    lean_dec(v___y_3599_);
    lean_dec_ref(v___y_3598_);
    lean_dec(v___y_3597_);
    lean_dec_ref(v___y_3596_);
    return v_res_3602_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(
    mut v___x_3603_: *mut LeanObject,
    mut v___y_3604_: *mut LeanObject,
    mut v___y_3605_: *mut LeanObject,
    mut v___y_3606_: *mut LeanObject,
    mut v___y_3607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    v___x_3609_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3609_, 0, v___x_3603_);
    return v___x_3609_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1___boxed(
    mut v___x_3610_: *mut LeanObject,
    mut v___y_3611_: *mut LeanObject,
    mut v___y_3612_: *mut LeanObject,
    mut v___y_3613_: *mut LeanObject,
    mut v___y_3614_: *mut LeanObject,
    mut v___y_3615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3616_: *mut LeanObject = core::ptr::null_mut();
    v_res_3616_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__1(
        v___x_3610_,
        v___y_3611_,
        v___y_3612_,
        v___y_3613_,
        v___y_3614_,
    );
    lean_dec(v___y_3614_);
    lean_dec_ref(v___y_3613_);
    lean_dec(v___y_3612_);
    lean_dec_ref(v___y_3611_);
    return v_res_3616_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(
    mut v___x_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
    mut v___y_3619_: *mut LeanObject,
    mut v___y_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    v___x_3623_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3623_, 0, v___x_3617_);
    return v___x_3623_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed(
    mut v___x_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
    mut v___y_3629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3630_: *mut LeanObject = core::ptr::null_mut();
    v_res_3630_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2(
        v___x_3624_,
        v___y_3625_,
        v___y_3626_,
        v___y_3627_,
        v___y_3628_,
    );
    lean_dec(v___y_3628_);
    lean_dec_ref(v___y_3627_);
    lean_dec(v___y_3626_);
    lean_dec_ref(v___y_3625_);
    return v_res_3630_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    v___x_3631_ = lean_unsigned_to_nat(32);
    v___x_3632_ = lean_mk_empty_array_with_capacity(v___x_3631_);
    v___x_3633_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3633_, 0, v___x_3632_);
    return v___x_3633_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3634_: usize = 0;
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    v___x_3634_ = 5usize;
    v___x_3635_ = lean_unsigned_to_nat(0);
    v___x_3636_ = lean_unsigned_to_nat(32);
    v___x_3637_ = lean_mk_empty_array_with_capacity(v___x_3636_);
    v___x_3638_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__0);
    v___x_3639_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3639_, 0, v___x_3638_);
    lean_ctor_set(v___x_3639_, 1, v___x_3637_);
    lean_ctor_set(v___x_3639_, 2, v___x_3635_);
    lean_ctor_set(v___x_3639_, 3, v___x_3635_);
    lean_ctor_set_usize(v___x_3639_, 4, v___x_3634_);
    return v___x_3639_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(
    mut v___y_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v_enabled_3658_: u8 = 0;
    let mut v_assignment_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3673_: u8 = 0;
    let mut v_unused_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3642_ = lean_st_ref_get(v___y_3640_);
                v_infoState_3643_ = lean_ctor_get(v___x_3642_, 7);
                lean_inc_ref(v_infoState_3643_);
                lean_dec(v___x_3642_);
                v_trees_3644_ = lean_ctor_get(v_infoState_3643_, 2);
                lean_inc_ref(v_trees_3644_);
                lean_dec_ref(v_infoState_3643_);
                v___x_3645_ = lean_st_ref_take(v___y_3640_);
                v_infoState_3646_ = lean_ctor_get(v___x_3645_, 7);
                v_env_3647_ = lean_ctor_get(v___x_3645_, 0);
                v_nextMacroScope_3648_ = lean_ctor_get(v___x_3645_, 1);
                v_ngen_3649_ = lean_ctor_get(v___x_3645_, 2);
                v_auxDeclNGen_3650_ = lean_ctor_get(v___x_3645_, 3);
                v_traceState_3651_ = lean_ctor_get(v___x_3645_, 4);
                v_cache_3652_ = lean_ctor_get(v___x_3645_, 5);
                v_messages_3653_ = lean_ctor_get(v___x_3645_, 6);
                v_snapshotTasks_3654_ = lean_ctor_get(v___x_3645_, 8);
                v_isSharedCheck_3675_ = (!lean_is_exclusive(v___x_3645_)) as u8;
                if v_isSharedCheck_3675_ == 0 {
                    v___x_3656_ = v___x_3645_;
                    v_isShared_3657_ = v_isSharedCheck_3675_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3654_);
                    lean_inc(v_infoState_3646_);
                    lean_inc(v_messages_3653_);
                    lean_inc(v_cache_3652_);
                    lean_inc(v_traceState_3651_);
                    lean_inc(v_auxDeclNGen_3650_);
                    lean_inc(v_ngen_3649_);
                    lean_inc(v_nextMacroScope_3648_);
                    lean_inc(v_env_3647_);
                    lean_dec(v___x_3645_);
                    v___x_3656_ = lean_box(0);
                    v_isShared_3657_ = v_isSharedCheck_3675_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_3658_ = lean_ctor_get_uint8(
                    v_infoState_3646_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_3659_ = lean_ctor_get(v_infoState_3646_, 0);
                v_lazyAssignment_3660_ = lean_ctor_get(v_infoState_3646_, 1);
                v_isSharedCheck_3673_ = (!lean_is_exclusive(v_infoState_3646_)) as u8;
                if v_isSharedCheck_3673_ == 0 {
                    v_unused_3674_ = lean_ctor_get(v_infoState_3646_, 2);
                    lean_dec(v_unused_3674_);
                    v___x_3662_ = v_infoState_3646_;
                    v_isShared_3663_ = v_isSharedCheck_3673_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_3660_);
                    lean_inc(v_assignment_3659_);
                    lean_dec(v_infoState_3646_);
                    v___x_3662_ = lean_box(0);
                    v_isShared_3663_ = v_isSharedCheck_3673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3664_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___closed__1);
                if v_isShared_3663_ == 0 {
                    lean_ctor_set(v___x_3662_, 2, v___x_3664_);
                    v___x_3666_ = v___x_3662_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3672_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_assignment_3659_);
                    lean_ctor_set(v_reuseFailAlloc_3672_, 1, v_lazyAssignment_3660_);
                    lean_ctor_set(v_reuseFailAlloc_3672_, 2, v___x_3664_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3672_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_3658_,
                    );
                    v___x_3666_ = v_reuseFailAlloc_3672_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3657_ == 0 {
                    lean_ctor_set(v___x_3656_, 7, v___x_3666_);
                    v___x_3668_ = v___x_3656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_env_3647_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 1, v_nextMacroScope_3648_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 2, v_ngen_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 3, v_auxDeclNGen_3650_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 4, v_traceState_3651_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 5, v_cache_3652_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 6, v_messages_3653_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 7, v___x_3666_);
                    lean_ctor_set(v_reuseFailAlloc_3671_, 8, v_snapshotTasks_3654_);
                    v___x_3668_ = v_reuseFailAlloc_3671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3669_ = lean_st_ref_set(v___y_3640_, v___x_3668_);
                v___x_3670_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3670_, 0, v_trees_3644_);
                return v___x_3670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg___boxed(
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3678_: *mut LeanObject = core::ptr::null_mut();
    v_res_3678_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_3676_);
    lean_dec(v___y_3676_);
    return v_res_3678_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(
    mut v_mkInfoOnError_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
    mut v___y_3681_: *mut LeanObject,
    mut v___y_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
    mut v___f_3684_: *mut LeanObject,
    mut v_mkInfo_3685_: *mut LeanObject,
    mut v_a_x3f_3686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3699_: u8 = 0;
    let mut v_val_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3707_: u8 = 0;
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_x3f_3686_) == 0 {
                    lean_dec_ref(v_mkInfo_3685_);
                    lean_inc(v___y_3683_);
                    lean_inc_ref(v___y_3682_);
                    lean_inc(v___y_3681_);
                    lean_inc_ref(v___y_3680_);
                    v___x_3688_ = lean_apply_5(
                        v_mkInfoOnError_3679_,
                        v___y_3680_,
                        v___y_3681_,
                        v___y_3682_,
                        v___y_3683_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3688_) == 0 {
                        v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
                        lean_inc(v_a_3689_);
                        lean_dec_ref_known(v___x_3688_, 1);
                        v___x_3690_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3690_, 0, v_a_3689_);
                        lean_inc(v___y_3683_);
                        lean_inc_ref(v___y_3682_);
                        lean_inc(v___y_3681_);
                        lean_inc_ref(v___y_3680_);
                        v___x_3691_ = lean_apply_6(
                            v___f_3684_,
                            v___x_3690_,
                            v___y_3680_,
                            v___y_3681_,
                            v___y_3682_,
                            v___y_3683_,
                            lean_box(0),
                        );
                        return v___x_3691_;
                    } else {
                        lean_dec_ref(v___f_3684_);
                        v_a_3692_ = lean_ctor_get(v___x_3688_, 0);
                        v_isSharedCheck_3699_ = (!lean_is_exclusive(v___x_3688_)) as u8;
                        if v_isSharedCheck_3699_ == 0 {
                            v___x_3694_ = v___x_3688_;
                            v_isShared_3695_ = v_isSharedCheck_3699_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3692_);
                            lean_dec(v___x_3688_);
                            v___x_3694_ = lean_box(0);
                            v_isShared_3695_ = v_isSharedCheck_3699_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_mkInfoOnError_3679_);
                    v_val_3700_ = lean_ctor_get(v_a_x3f_3686_, 0);
                    lean_inc(v_val_3700_);
                    lean_dec_ref_known(v_a_x3f_3686_, 1);
                    lean_inc(v___y_3683_);
                    lean_inc_ref(v___y_3682_);
                    lean_inc(v___y_3681_);
                    lean_inc_ref(v___y_3680_);
                    v___x_3701_ = lean_apply_6(
                        v_mkInfo_3685_,
                        v_val_3700_,
                        v___y_3680_,
                        v___y_3681_,
                        v___y_3682_,
                        v___y_3683_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_3701_) == 0 {
                        v_a_3702_ = lean_ctor_get(v___x_3701_, 0);
                        lean_inc(v_a_3702_);
                        lean_dec_ref_known(v___x_3701_, 1);
                        lean_inc(v___y_3683_);
                        lean_inc_ref(v___y_3682_);
                        lean_inc(v___y_3681_);
                        lean_inc_ref(v___y_3680_);
                        v___x_3703_ = lean_apply_6(
                            v___f_3684_,
                            v_a_3702_,
                            v___y_3680_,
                            v___y_3681_,
                            v___y_3682_,
                            v___y_3683_,
                            lean_box(0),
                        );
                        return v___x_3703_;
                    } else {
                        lean_dec_ref(v___f_3684_);
                        v_a_3704_ = lean_ctor_get(v___x_3701_, 0);
                        v_isSharedCheck_3711_ = (!lean_is_exclusive(v___x_3701_)) as u8;
                        if v_isSharedCheck_3711_ == 0 {
                            v___x_3706_ = v___x_3701_;
                            v_isShared_3707_ = v_isSharedCheck_3711_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3704_);
                            lean_dec(v___x_3701_);
                            v___x_3706_ = lean_box(0);
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
                    v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
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
                    v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
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
    mut v_mkInfoOnError_3712_: *mut LeanObject,
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
    mut v___y_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___f_3717_: *mut LeanObject,
    mut v_mkInfo_3718_: *mut LeanObject,
    mut v_a_x3f_3719_: *mut LeanObject,
    mut v___y_3720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3721_: *mut LeanObject = core::ptr::null_mut();
    v_res_3721_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___f_3717_, v_mkInfo_3718_, v_a_x3f_3719_);
    lean_dec(v___y_3716_);
    lean_dec_ref(v___y_3715_);
    lean_dec(v___y_3714_);
    lean_dec_ref(v___y_3713_);
    return v_res_3721_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(
    mut v_a_3722_: *mut LeanObject,
    mut v_info_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
    mut v___y_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___y_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_3750_: u8 = 0;
    let mut v_assignment_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3756_: u8 = 0;
    let mut v_val_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3763_: u8 = 0;
    let mut v_enabled_3764_: u8 = 0;
    let mut v_assignment_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3769_: u8 = 0;
    let mut v_val_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut v_isSharedCheck_3782_: u8 = 0;
    let mut v_unused_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3729_ = lean_st_ref_take(v___y_3727_);
                v_env_3730_ = lean_ctor_get(v___x_3729_, 0);
                v_nextMacroScope_3731_ = lean_ctor_get(v___x_3729_, 1);
                v_ngen_3732_ = lean_ctor_get(v___x_3729_, 2);
                v_auxDeclNGen_3733_ = lean_ctor_get(v___x_3729_, 3);
                v_traceState_3734_ = lean_ctor_get(v___x_3729_, 4);
                v_cache_3735_ = lean_ctor_get(v___x_3729_, 5);
                v_messages_3736_ = lean_ctor_get(v___x_3729_, 6);
                v_infoState_3737_ = lean_ctor_get(v___x_3729_, 7);
                v_snapshotTasks_3738_ = lean_ctor_get(v___x_3729_, 8);
                v_isSharedCheck_3784_ = (!lean_is_exclusive(v___x_3729_)) as u8;
                if v_isSharedCheck_3784_ == 0 {
                    v___x_3740_ = v___x_3729_;
                    v_isShared_3741_ = v_isSharedCheck_3784_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3738_);
                    lean_inc(v_infoState_3737_);
                    lean_inc(v_messages_3736_);
                    lean_inc(v_cache_3735_);
                    lean_inc(v_traceState_3734_);
                    lean_inc(v_auxDeclNGen_3733_);
                    lean_inc(v_ngen_3732_);
                    lean_inc(v_nextMacroScope_3731_);
                    lean_inc(v_env_3730_);
                    lean_dec(v___x_3729_);
                    v___x_3740_ = lean_box(0);
                    v_isShared_3741_ = v_isSharedCheck_3784_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_info_3723_) == 0 {
                    v_enabled_3750_ = lean_ctor_get_uint8(
                        v_infoState_3737_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_assignment_3751_ = lean_ctor_get(v_infoState_3737_, 0);
                    v_lazyAssignment_3752_ = lean_ctor_get(v_infoState_3737_, 1);
                    v_trees_3753_ = lean_ctor_get(v_infoState_3737_, 2);
                    v_isSharedCheck_3763_ = (!lean_is_exclusive(v_infoState_3737_)) as u8;
                    if v_isSharedCheck_3763_ == 0 {
                        v___x_3755_ = v_infoState_3737_;
                        v_isShared_3756_ = v_isSharedCheck_3763_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_trees_3753_);
                        lean_inc(v_lazyAssignment_3752_);
                        lean_inc(v_assignment_3751_);
                        lean_dec(v_infoState_3737_);
                        v___x_3755_ = lean_box(0);
                        v_isShared_3756_ = v_isSharedCheck_3763_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_enabled_3764_ = lean_ctor_get_uint8(
                        v_infoState_3737_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_assignment_3765_ = lean_ctor_get(v_infoState_3737_, 0);
                    v_lazyAssignment_3766_ = lean_ctor_get(v_infoState_3737_, 1);
                    v_isSharedCheck_3782_ = (!lean_is_exclusive(v_infoState_3737_)) as u8;
                    if v_isSharedCheck_3782_ == 0 {
                        v_unused_3783_ = lean_ctor_get(v_infoState_3737_, 2);
                        lean_dec(v_unused_3783_);
                        v___x_3768_ = v_infoState_3737_;
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_lazyAssignment_3766_);
                        lean_inc(v_assignment_3765_);
                        lean_dec(v_infoState_3737_);
                        v___x_3768_ = lean_box(0);
                        v_isShared_3769_ = v_isSharedCheck_3782_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3741_ == 0 {
                    lean_ctor_set(v___x_3740_, 7, v___y_3743_);
                    v___x_3745_ = v___x_3740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_env_3730_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 1, v_nextMacroScope_3731_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 2, v_ngen_3732_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 3, v_auxDeclNGen_3733_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 4, v_traceState_3734_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 5, v_cache_3735_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 6, v_messages_3736_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 7, v___y_3743_);
                    lean_ctor_set(v_reuseFailAlloc_3749_, 8, v_snapshotTasks_3738_);
                    v___x_3745_ = v_reuseFailAlloc_3749_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3746_ = lean_st_ref_set(v___y_3727_, v___x_3745_);
                v___x_3747_ = lean_box(0);
                v___x_3748_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3748_, 0, v___x_3747_);
                return v___x_3748_;
            }
            4 => {
                v_val_3757_ = lean_ctor_get(v_info_3723_, 0);
                lean_inc(v_val_3757_);
                lean_dec_ref_known(v_info_3723_, 1);
                v___x_3758_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3758_, 0, v_val_3757_);
                lean_ctor_set(v___x_3758_, 1, v_trees_3753_);
                v___x_3759_ = l_Lean_PersistentArray_push___redArg(v_a_3722_, v___x_3758_);
                if v_isShared_3756_ == 0 {
                    lean_ctor_set(v___x_3755_, 2, v___x_3759_);
                    v___x_3761_ = v___x_3755_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_assignment_3751_);
                    lean_ctor_set(v_reuseFailAlloc_3762_, 1, v_lazyAssignment_3752_);
                    lean_ctor_set(v_reuseFailAlloc_3762_, 2, v___x_3759_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3762_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
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
                v_val_3770_ = lean_ctor_get(v_info_3723_, 0);
                v_isSharedCheck_3781_ = (!lean_is_exclusive(v_info_3723_)) as u8;
                if v_isSharedCheck_3781_ == 0 {
                    v___x_3772_ = v_info_3723_;
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_val_3770_);
                    lean_dec(v_info_3723_);
                    v___x_3772_ = lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3781_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3773_ == 0 {
                    lean_ctor_set_tag(v___x_3772_, 2);
                    v___x_3775_ = v___x_3772_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_val_3770_);
                    v___x_3775_ = v_reuseFailAlloc_3780_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3776_ = l_Lean_PersistentArray_push___redArg(v_a_3722_, v___x_3775_);
                if v_isShared_3769_ == 0 {
                    lean_ctor_set(v___x_3768_, 2, v___x_3776_);
                    v___x_3778_ = v___x_3768_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_assignment_3765_);
                    lean_ctor_set(v_reuseFailAlloc_3779_, 1, v_lazyAssignment_3766_);
                    lean_ctor_set(v_reuseFailAlloc_3779_, 2, v___x_3776_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3779_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
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
    mut v_a_3785_: *mut LeanObject,
    mut v_info_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
    mut v___y_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
    mut v___y_3791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3792_: *mut LeanObject = core::ptr::null_mut();
    v_res_3792_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0(v_a_3785_, v_info_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
    lean_dec(v___y_3790_);
    lean_dec_ref(v___y_3789_);
    lean_dec(v___y_3788_);
    lean_dec_ref(v___y_3787_);
    return v_res_3792_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(
    mut v_x_3793_: *mut LeanObject,
    mut v_mkInfo_3794_: *mut LeanObject,
    mut v_mkInfoOnError_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
    mut v___y_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_3803_: u8 = 0;
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v_unused_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut v_reuseFailAlloc_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3833_: u8 = 0;
    let mut v_a_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_unused_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3848_: u8 = 0;
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3801_ = lean_st_ref_get(v___y_3799_);
                v_infoState_3802_ = lean_ctor_get(v___x_3801_, 7);
                lean_inc_ref(v_infoState_3802_);
                lean_dec(v___x_3801_);
                v_enabled_3803_ = lean_ctor_get_uint8(
                    v_infoState_3802_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_3802_);
                if v_enabled_3803_ == 0 {
                    lean_dec_ref(v_mkInfoOnError_3795_);
                    lean_dec_ref(v_mkInfo_3794_);
                    lean_inc(v___y_3799_);
                    lean_inc_ref(v___y_3798_);
                    lean_inc(v___y_3797_);
                    lean_inc_ref(v___y_3796_);
                    v___x_3804_ = lean_apply_5(
                        v_x_3793_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        lean_box(0),
                    );
                    return v___x_3804_;
                } else {
                    v___x_3805_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_3799_);
                    v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
                    lean_inc(v_a_3806_);
                    lean_dec_ref(v___x_3805_);
                    v___f_3807_ = lean_alloc_closure(l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    lean_closure_set(v___f_3807_, 0, v_a_3806_);
                    lean_inc(v___y_3799_);
                    lean_inc_ref(v___y_3798_);
                    lean_inc(v___y_3797_);
                    lean_inc_ref(v___y_3796_);
                    v_r_3808_ = lean_apply_5(
                        v_x_3793_,
                        v___y_3796_,
                        v___y_3797_,
                        v___y_3798_,
                        v___y_3799_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_3808_) == 0 {
                        v_a_3809_ = lean_ctor_get(v_r_3808_, 0);
                        v_isSharedCheck_3833_ = (!lean_is_exclusive(v_r_3808_)) as u8;
                        if v_isSharedCheck_3833_ == 0 {
                            v___x_3811_ = v_r_3808_;
                            v_isShared_3812_ = v_isSharedCheck_3833_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3809_);
                            lean_dec(v_r_3808_);
                            v___x_3811_ = lean_box(0);
                            v_isShared_3812_ = v_isSharedCheck_3833_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3834_ = lean_ctor_get(v_r_3808_, 0);
                        lean_inc(v_a_3834_);
                        lean_dec_ref_known(v_r_3808_, 1);
                        v___x_3835_ = lean_box(0);
                        v___x_3836_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___f_3807_, v_mkInfo_3794_, v___x_3835_);
                        if lean_obj_tag(v___x_3836_) == 0 {
                            v_isSharedCheck_3843_ = (!lean_is_exclusive(v___x_3836_)) as u8;
                            if v_isSharedCheck_3843_ == 0 {
                                v_unused_3844_ = lean_ctor_get(v___x_3836_, 0);
                                lean_dec(v_unused_3844_);
                                v___x_3838_ = v___x_3836_;
                                v_isShared_3839_ = v_isSharedCheck_3843_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_3836_);
                                v___x_3838_ = lean_box(0);
                                v_isShared_3839_ = v_isSharedCheck_3843_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3834_);
                            v_a_3845_ = lean_ctor_get(v___x_3836_, 0);
                            v_isSharedCheck_3852_ = (!lean_is_exclusive(v___x_3836_)) as u8;
                            if v_isSharedCheck_3852_ == 0 {
                                v___x_3847_ = v___x_3836_;
                                v_isShared_3848_ = v_isSharedCheck_3852_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_3845_);
                                lean_dec(v___x_3836_);
                                v___x_3847_ = lean_box(0);
                                v_isShared_3848_ = v_isSharedCheck_3852_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_3809_);
                if v_isShared_3812_ == 0 {
                    lean_ctor_set_tag(v___x_3811_, 1);
                    v___x_3814_ = v___x_3811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3809_);
                    v___x_3814_ = v_reuseFailAlloc_3832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3815_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg___lam__1(v_mkInfoOnError_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___f_3807_, v_mkInfo_3794_, v___x_3814_);
                if lean_obj_tag(v___x_3815_) == 0 {
                    v_isSharedCheck_3822_ = (!lean_is_exclusive(v___x_3815_)) as u8;
                    if v_isSharedCheck_3822_ == 0 {
                        v_unused_3823_ = lean_ctor_get(v___x_3815_, 0);
                        lean_dec(v_unused_3823_);
                        v___x_3817_ = v___x_3815_;
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_3815_);
                        v___x_3817_ = lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3822_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3809_);
                    v_a_3824_ = lean_ctor_get(v___x_3815_, 0);
                    v_isSharedCheck_3831_ = (!lean_is_exclusive(v___x_3815_)) as u8;
                    if v_isSharedCheck_3831_ == 0 {
                        v___x_3826_ = v___x_3815_;
                        v_isShared_3827_ = v_isSharedCheck_3831_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3824_);
                        lean_dec(v___x_3815_);
                        v___x_3826_ = lean_box(0);
                        v_isShared_3827_ = v_isSharedCheck_3831_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3818_ == 0 {
                    lean_ctor_set(v___x_3817_, 0, v_a_3809_);
                    v___x_3820_ = v___x_3817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3809_);
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
                    v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
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
                    lean_ctor_set_tag(v___x_3838_, 1);
                    lean_ctor_set(v___x_3838_, 0, v_a_3834_);
                    v___x_3841_ = v___x_3838_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3834_);
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
                    v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
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
    mut v_x_3853_: *mut LeanObject,
    mut v_mkInfo_3854_: *mut LeanObject,
    mut v_mkInfoOnError_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3861_: *mut LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_3853_, v_mkInfo_3854_, v_mkInfoOnError_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
    lean_dec(v___y_3859_);
    lean_dec_ref(v___y_3858_);
    lean_dec(v___y_3857_);
    lean_dec_ref(v___y_3856_);
    return v_res_3861_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo(
    mut v_stx_3864_: *mut LeanObject,
    mut v_lctx_3865_: *mut LeanObject,
    mut v_expr_3866_: *mut LeanObject,
    mut v_expectedType_x3f_3867_: *mut LeanObject,
    mut v_isBinder_3868_: u8,
    mut v_a_3869_: *mut LeanObject,
    mut v_a_3870_: *mut LeanObject,
    mut v_a_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    v___x_3874_ = lean_box((v_isBinder_3868_) as usize);
    lean_inc(v_expectedType_x3f_3867_);
    lean_inc_ref(v_lctx_3865_);
    lean_inc(v_stx_3864_);
    v___f_3875_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__0___boxed as *mut core::ffi::c_void,
        11,
        5,
    );
    lean_closure_set(v___f_3875_, 0, v_stx_3864_);
    lean_closure_set(v___f_3875_, 1, v_lctx_3865_);
    lean_closure_set(v___f_3875_, 2, v_expectedType_x3f_3867_);
    lean_closure_set(v___f_3875_, 3, v_expr_3866_);
    lean_closure_set(v___f_3875_, 4, v___x_3874_);
    v___f_3876_ = l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___closed__0;
    v___x_3877_ = lean_box(0);
    v___x_3878_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3878_, 0, v___x_3877_);
    lean_ctor_set(v___x_3878_, 1, v_stx_3864_);
    v___x_3879_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3879_, 0, v___x_3878_);
    lean_ctor_set(v___x_3879_, 1, v_lctx_3865_);
    lean_ctor_set(v___x_3879_, 2, v_expectedType_x3f_3867_);
    v___x_3880_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_3880_, 0, v___x_3879_);
    v___f_3881_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___lam__2___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3881_, 0, v___x_3880_);
    v___x_3882_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v___f_3876_, v___f_3875_, v___f_3881_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
    return v___x_3882_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo___boxed(
    mut v_stx_3883_: *mut LeanObject,
    mut v_lctx_3884_: *mut LeanObject,
    mut v_expr_3885_: *mut LeanObject,
    mut v_expectedType_x3f_3886_: *mut LeanObject,
    mut v_isBinder_3887_: *mut LeanObject,
    mut v_a_3888_: *mut LeanObject,
    mut v_a_3889_: *mut LeanObject,
    mut v_a_3890_: *mut LeanObject,
    mut v_a_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isBinder_boxed_3893_: u8 = 0;
    let mut v_res_3894_: *mut LeanObject = core::ptr::null_mut();
    v_isBinder_boxed_3893_ = (lean_unbox(v_isBinder_3887_) as u8);
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
    lean_dec(v_a_3891_);
    lean_dec_ref(v_a_3890_);
    lean_dec(v_a_3889_);
    lean_dec_ref(v_a_3888_);
    return v_res_3894_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(
    mut v___y_3895_: *mut LeanObject,
    mut v___y_3896_: *mut LeanObject,
    mut v___y_3897_: *mut LeanObject,
    mut v___y_3898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    v___x_3900_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___redArg(v___y_3898_);
    return v___x_3900_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0___boxed(
    mut v___y_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
    mut v___y_3904_: *mut LeanObject,
    mut v___y_3905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3906_: *mut LeanObject = core::ptr::null_mut();
    v_res_3906_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0_spec__0(v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
    lean_dec(v___y_3904_);
    lean_dec_ref(v___y_3903_);
    lean_dec(v___y_3902_);
    lean_dec_ref(v___y_3901_);
    return v_res_3906_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(
    mut v_00_u03b1_3907_: *mut LeanObject,
    mut v_x_3908_: *mut LeanObject,
    mut v_mkInfo_3909_: *mut LeanObject,
    mut v_mkInfoOnError_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    v___x_3916_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___redArg(v_x_3908_, v_mkInfo_3909_, v_mkInfoOnError_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
    return v___x_3916_;
}
pub unsafe fn l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0___boxed(
    mut v_00_u03b1_3917_: *mut LeanObject,
    mut v_x_3918_: *mut LeanObject,
    mut v_mkInfo_3919_: *mut LeanObject,
    mut v_mkInfoOnError_3920_: *mut LeanObject,
    mut v___y_3921_: *mut LeanObject,
    mut v___y_3922_: *mut LeanObject,
    mut v___y_3923_: *mut LeanObject,
    mut v___y_3924_: *mut LeanObject,
    mut v___y_3925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3926_: *mut LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Lean_Elab_withInfoContext_x27___at___00Lean_Elab_Tactic_Do_ProofMode_addLocalVarInfo_spec__0(v_00_u03b1_3917_, v_x_3918_, v_mkInfo_3919_, v_mkInfoOnError_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
    lean_dec(v___y_3924_);
    lean_dec_ref(v___y_3923_);
    lean_dec(v___y_3922_);
    lean_dec_ref(v___y_3921_);
    return v_res_3926_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
    mut v_stx_3933_: *mut LeanObject,
    mut v_00_u03c3s_3934_: *mut LeanObject,
    mut v_hyp_3935_: *mut LeanObject,
    mut v_isBinder_3936_: u8,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: u8 = 0;
    let mut v___x_3951_: u8 = 0;
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3959_: u8 = 0;
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3962_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3943_) == 0 {
                    v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
                    lean_inc(v_a_3944_);
                    lean_dec_ref_known(v___x_3943_, 1);
                    v_lctx_3945_ = lean_ctor_get(v_a_3937_, 2);
                    v_name_3946_ = lean_ctor_get(v_hyp_3935_, 0);
                    lean_inc(v_name_3946_);
                    v_uniq_3947_ = lean_ctor_get(v_hyp_3935_, 1);
                    lean_inc_n(v_uniq_3947_, 2);
                    v_p_3948_ = lean_ctor_get(v_hyp_3935_, 2);
                    lean_inc_ref(v_p_3948_);
                    lean_dec_ref(v_hyp_3935_);
                    v___x_3949_ = l_Lean_mkAppB(v_a_3944_, v_00_u03c3s_3934_, v_p_3948_);
                    v___x_3950_ = 0;
                    v___x_3951_ = 0;
                    lean_inc_ref(v___x_3949_);
                    lean_inc_ref(v_lctx_3945_);
                    v___x_3952_ = l_Lean_LocalContext_mkLocalDecl(
                        v_lctx_3945_,
                        v_uniq_3947_,
                        v_name_3946_,
                        v___x_3949_,
                        v___x_3950_,
                        v___x_3951_,
                    );
                    v___x_3953_ = l_Lean_Expr_fvar___override(v_uniq_3947_);
                    v___x_3954_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3954_, 0, v___x_3949_);
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
                    lean_dec_ref(v_hyp_3935_);
                    lean_dec_ref(v_00_u03c3s_3934_);
                    lean_dec(v_stx_3933_);
                    v_a_3956_ = lean_ctor_get(v___x_3943_, 0);
                    v_isSharedCheck_3963_ = (!lean_is_exclusive(v___x_3943_)) as u8;
                    if v_isSharedCheck_3963_ == 0 {
                        v___x_3958_ = v___x_3943_;
                        v_isShared_3959_ = v_isSharedCheck_3963_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3956_);
                        lean_dec(v___x_3943_);
                        v___x_3958_ = lean_box(0);
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
                    v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
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
    mut v_stx_3964_: *mut LeanObject,
    mut v_00_u03c3s_3965_: *mut LeanObject,
    mut v_hyp_3966_: *mut LeanObject,
    mut v_isBinder_3967_: *mut LeanObject,
    mut v_a_3968_: *mut LeanObject,
    mut v_a_3969_: *mut LeanObject,
    mut v_a_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isBinder_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut LeanObject = core::ptr::null_mut();
    v_isBinder_boxed_3973_ = (lean_unbox(v_isBinder_3967_) as u8);
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
    lean_dec(v_a_3971_);
    lean_dec_ref(v_a_3970_);
    lean_dec(v_a_3969_);
    lean_dec_ref(v_a_3968_);
    return v_res_3974_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_SPred_DerivedLaws(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_Do_ProofMode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default();
    lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal_default);
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal();
    lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedMGoal);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_SPred_DerivedLaws(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_Do_ProofMode(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
}
