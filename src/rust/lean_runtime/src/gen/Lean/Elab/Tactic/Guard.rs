// Lean compiler output
// Module: Lean.Elab.Tactic.Guard
// Imports: Init.Guard Lean.Elab.Command Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Guard::{initialize_Init_Guard, runtime_initialize_Init_Guard};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_5, lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value: LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value: LeanStringObject<6> =
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
        m_data: [99, 111, 108, 111, 110, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__2_value)
                as *mut LeanObject,
            16701333901772390046 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value: LeanStringObject<7> =
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
        m_data: [99, 111, 108, 111, 110, 82, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__4_value)
                as *mut LeanObject,
            11766820169793439539 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value: LeanStringObject<7> =
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
        m_data: [99, 111, 108, 111, 110, 68, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__6_value)
                as *mut LeanObject,
            4334716130055557871 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value: LeanStringObject<7> =
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
        m_data: [99, 111, 108, 111, 110, 83, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__8_value)
                as *mut LeanObject,
            16142497725452366017 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value: LeanStringObject<7> =
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
        m_data: [99, 111, 108, 111, 110, 65, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__10_value)
                as *mut LeanObject,
            2800469225767172270 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 1,
        },
        m_objs: [1 as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__14_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 1,
        },
        m_objs: [2 as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__16_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value: LeanStringObject<8> =
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
        m_data: [99, 111, 108, 111, 110, 69, 113, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__0_value)
                as *mut LeanObject,
            3454211822294123381 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value: LeanStringObject<9> =
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
        m_data: [99, 111, 108, 111, 110, 69, 113, 82, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__2_value)
                as *mut LeanObject,
            4547212498149662503 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value: LeanStringObject<9> =
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
        m_data: [99, 111, 108, 111, 110, 69, 113, 68, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__4_value)
                as *mut LeanObject,
            9469198591938552093 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value: LeanStringObject<9> =
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
        m_data: [99, 111, 108, 111, 110, 69, 113, 83, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__6_value)
                as *mut LeanObject,
            18100060585123032661 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value: LeanStringObject<9> =
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
        m_data: [99, 111, 108, 111, 110, 69, 113, 65, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__8_value)
                as *mut LeanObject,
            398647838421166144 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value: LeanStringObject<6> =
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
        m_data: [101, 113, 117, 97, 108, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__0_value)
                as *mut LeanObject,
            17604351797772570779 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value: LeanStringObject<7> =
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
        m_data: [101, 113, 117, 97, 108, 82, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__2_value)
                as *mut LeanObject,
            17078963301316888828 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value: LeanStringObject<7> =
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
        m_data: [101, 113, 117, 97, 108, 68, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__4_value)
                as *mut LeanObject,
            9006235547594326259 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value: LeanStringObject<7> =
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
        m_data: [101, 113, 117, 97, 108, 83, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__6_value)
                as *mut LeanObject,
            13788227380297645704 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value: LeanStringObject<7> =
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
        m_data: [101, 113, 117, 97, 108, 65, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__8_value)
                as *mut LeanObject,
            8682205543839346023 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0_value:
    LeanStringObject<23> = LeanStringObject {
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
        115, 121, 110, 116, 97, 99, 116, 105, 99, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108,
        32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1_value:
    LeanStringObject<50> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3_value:
    LeanStringObject<56> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4_value:
    LeanStringObject<46> = LeanStringObject {
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
        100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97,
        108, 32, 40, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 105, 110, 115, 116, 97, 110,
        99, 101, 115, 41, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5_value:
    LeanStringObject<54> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6_value:
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
        97, 108, 112, 104, 97, 45, 101, 113, 117, 105, 118, 97, 108, 101, 110, 116, 32, 116, 111, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2_value: LeanStringObject<
    10,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value: LeanStringObject<10> =
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
        m_data: [103, 117, 97, 114, 100, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__1_value)
                as *mut LeanObject,
            2406710036554907729 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__3_value)
                as *mut LeanObject,
            17520459286155217955 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [71, 117, 97, 114, 100, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 69, 120, 112, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__2_value) as *mut LeanObject,58792184315864126 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 75 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 82 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 75 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 75 as usize) << 1) | 1) as *mut LeanObject,((( 17 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__4_value) as *mut LeanObject,((( 17 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 69, 120, 112, 114, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__0_value) as *mut LeanObject,2900613087037517015 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__1_value) as *mut LeanObject,((( 47 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 86 as usize) << 1) | 1) as *mut LeanObject,((( 21 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__4_value) as *mut LeanObject,((( 21 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value: LeanStringObject<12> =
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
        m_data: [103, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__0_value)
                as *mut LeanObject,
            9705855369448785090 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value: LeanStringObject<16> =
    LeanStringObject {
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
            103, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 67, 111, 110, 118, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__2_value)
                as *mut LeanObject,
            1133233218418288393 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Conv_getLhs___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_getMainTarget___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__0_value) as *mut LeanObject,13924985917103118701 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 99 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 89 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__4_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 84, 97, 114, 103, 101, 116, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__0_value) as *mut LeanObject,3277492080379021737 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__1_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 103 as usize) << 1) | 1) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__4_value) as *mut LeanObject,((( 23 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0_value: LeanStringObject<
    23,
> = LeanStringObject {
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
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 108, 101, 116, 32, 98, 105, 110, 100, 105,
        110, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2_value: LeanStringObject<
    19,
> = LeanStringObject {
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
        96, 32, 105, 115, 32, 97, 32, 108, 101, 116, 32, 98, 105, 110, 100, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4_value: LeanStringObject<
    13,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8_value: LeanStringObject<
    32,
> = LeanStringObject {
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
        10, 98, 117, 116, 32, 119, 97, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116,
        111, 32, 104, 97, 118, 101, 32, 118, 97, 108, 117, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12_value: LeanStringObject<
    31,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value: LeanStringObject<9> =
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
        m_data: [103, 117, 97, 114, 100, 72, 121, 112, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__0_value)
                as *mut LeanObject,
            12801252452760768259 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value: LeanStringObject<13> =
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
        m_data: [103, 117, 97, 114, 100, 72, 121, 112, 67, 111, 110, 118, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__2_value)
                as *mut LeanObject,
            9950005495765075193 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 72, 121, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__0_value) as *mut LeanObject,10552425012879073248 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 106 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 130 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 106 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 106 as usize) << 1) | 1) as *mut LeanObject,((( 16 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__4_value) as *mut LeanObject,((( 16 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 72, 121, 112, 67, 111, 110, 118, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__0_value) as *mut LeanObject,283289726733858414 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut LeanObject,((( 45 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__1_value) as *mut LeanObject,((( 45 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 133 as usize) << 1) | 1) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__4_value) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value: LeanStringObject<8> =
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
        m_data: [67, 111, 109, 109, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value: LeanStringObject<13> =
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
        m_data: [103, 117, 97, 114, 100, 69, 120, 112, 114, 67, 109, 100, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__1_value)
                as *mut LeanObject,
            2836449611787596701 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 69, 120, 112, 114, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__0_value) as *mut LeanObject,14034849119720398400 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 136 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 143 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 136 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 136 as usize) << 1) | 1) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__4_value) as *mut LeanObject,((( 20 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2_value: LeanStringObject<
    28,
> = LeanStringObject {
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
        10, 100, 105, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116,
        111, 32, 96, 116, 114, 117, 101, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value: LeanStringObject<9> =
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
        m_data: [103, 117, 97, 114, 100, 67, 109, 100, 0],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__0_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__0_value)
                as *mut LeanObject,
            8409249086422357623 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 71, 117, 97, 114, 100, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__1_value) as *mut LeanObject,9301301477787065558 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__0_value) as *mut LeanObject,17344053803254828559 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 146 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 158 as usize) << 1) | 1) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__1_value) as *mut LeanObject,((( 31 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 146 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 146 as usize) << 1) | 1) as *mut LeanObject,((( 16 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__4_value) as *mut LeanObject,((( 16 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx(
    mut v_x_2484_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2484_) {
        0 => {
            let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
            v___x_2485_ = lean_unsigned_to_nat(0);
            return v___x_2485_;
        }
        1 => {
            let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
            v___x_2486_ = lean_unsigned_to_nat(1);
            return v___x_2486_;
        }
        _ => {
            let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
            v___x_2487_ = lean_unsigned_to_nat(2);
            return v___x_2487_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx___boxed(
    mut v_x_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2489_: *mut LeanObject = core::ptr::null_mut();
    v_res_2489_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorIdx(v_x_2488_);
    lean_dec(v_x_2488_);
    return v_res_2489_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(
    mut v_t_2490_: *mut LeanObject,
    mut v_k_2491_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_2490_) == 1 {
        let mut v_red_2492_: u8 = 0;
        let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
        v_red_2492_ = lean_ctor_get_uint8(v_t_2490_, 0 as u32);
        v___x_2493_ = lean_box((v_red_2492_) as usize);
        v___x_2494_ = lean_apply_1(v_k_2491_, v___x_2493_);
        return v___x_2494_;
    } else {
        return v_k_2491_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg___boxed(
    mut v_t_2495_: *mut LeanObject,
    mut v_k_2496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2497_: *mut LeanObject = core::ptr::null_mut();
    v_res_2497_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2495_, v_k_2496_);
    lean_dec(v_t_2495_);
    return v_res_2497_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(
    mut v_motive_2498_: *mut LeanObject,
    mut v_ctorIdx_2499_: *mut LeanObject,
    mut v_t_2500_: *mut LeanObject,
    mut v_h_2501_: *mut LeanObject,
    mut v_k_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    v___x_2503_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2500_, v_k_2502_);
    return v___x_2503_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___boxed(
    mut v_motive_2504_: *mut LeanObject,
    mut v_ctorIdx_2505_: *mut LeanObject,
    mut v_t_2506_: *mut LeanObject,
    mut v_h_2507_: *mut LeanObject,
    mut v_k_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2509_: *mut LeanObject = core::ptr::null_mut();
    v_res_2509_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim(
        v_motive_2504_,
        v_ctorIdx_2505_,
        v_t_2506_,
        v_h_2507_,
        v_k_2508_,
    );
    lean_dec(v_t_2506_);
    lean_dec(v_ctorIdx_2505_);
    return v_res_2509_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(
    mut v_t_2510_: *mut LeanObject,
    mut v_syntactic_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    v___x_2512_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2510_, v_syntactic_2511_);
    return v___x_2512_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg___boxed(
    mut v_t_2513_: *mut LeanObject,
    mut v_syntactic_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2515_: *mut LeanObject = core::ptr::null_mut();
    v_res_2515_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___redArg(
        v_t_2513_,
        v_syntactic_2514_,
    );
    lean_dec(v_t_2513_);
    return v_res_2515_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(
    mut v_motive_2516_: *mut LeanObject,
    mut v_t_2517_: *mut LeanObject,
    mut v_h_2518_: *mut LeanObject,
    mut v_syntactic_2519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    v___x_2520_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2517_, v_syntactic_2519_);
    return v___x_2520_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim___boxed(
    mut v_motive_2521_: *mut LeanObject,
    mut v_t_2522_: *mut LeanObject,
    mut v_h_2523_: *mut LeanObject,
    mut v_syntactic_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2525_: *mut LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_syntactic_elim(
        v_motive_2521_,
        v_t_2522_,
        v_h_2523_,
        v_syntactic_2524_,
    );
    lean_dec(v_t_2522_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(
    mut v_t_2526_: *mut LeanObject,
    mut v_defEq_2527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    v___x_2528_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2526_, v_defEq_2527_);
    return v___x_2528_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg___boxed(
    mut v_t_2529_: *mut LeanObject,
    mut v_defEq_2530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2531_: *mut LeanObject = core::ptr::null_mut();
    v_res_2531_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___redArg(v_t_2529_, v_defEq_2530_);
    lean_dec(v_t_2529_);
    return v_res_2531_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(
    mut v_motive_2532_: *mut LeanObject,
    mut v_t_2533_: *mut LeanObject,
    mut v_h_2534_: *mut LeanObject,
    mut v_defEq_2535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    v___x_2536_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2533_, v_defEq_2535_);
    return v___x_2536_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim___boxed(
    mut v_motive_2537_: *mut LeanObject,
    mut v_t_2538_: *mut LeanObject,
    mut v_h_2539_: *mut LeanObject,
    mut v_defEq_2540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2541_: *mut LeanObject = core::ptr::null_mut();
    v_res_2541_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_defEq_elim(
        v_motive_2537_,
        v_t_2538_,
        v_h_2539_,
        v_defEq_2540_,
    );
    lean_dec(v_t_2538_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(
    mut v_t_2542_: *mut LeanObject,
    mut v_alphaEq_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    v___x_2544_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2542_, v_alphaEq_2543_);
    return v___x_2544_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg___boxed(
    mut v_t_2545_: *mut LeanObject,
    mut v_alphaEq_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2547_: *mut LeanObject = core::ptr::null_mut();
    v_res_2547_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___redArg(v_t_2545_, v_alphaEq_2546_);
    lean_dec(v_t_2545_);
    return v_res_2547_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(
    mut v_motive_2548_: *mut LeanObject,
    mut v_t_2549_: *mut LeanObject,
    mut v_h_2550_: *mut LeanObject,
    mut v_alphaEq_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    v___x_2552_ =
        l_Lean_Elab_Tactic_GuardExpr_MatchKind_ctorElim___redArg(v_t_2549_, v_alphaEq_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim___boxed(
    mut v_motive_2553_: *mut LeanObject,
    mut v_t_2554_: *mut LeanObject,
    mut v_h_2555_: *mut LeanObject,
    mut v_alphaEq_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2557_: *mut LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_alphaEq_elim(
        v_motive_2553_,
        v_t_2554_,
        v_h_2555_,
        v_alphaEq_2556_,
    );
    lean_dec(v_t_2554_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(
    mut v_x_2597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    v___x_2598_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__3;
    lean_inc(v_x_2597_);
    v___x_2599_ = l_Lean_Syntax_isOfKind(v_x_2597_, v___x_2598_);
    if v___x_2599_ == 0 {
        let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2597_);
        v___x_2600_ = lean_box(0);
        return v___x_2600_;
    } else {
        let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2604_: u8 = 0;
        v___x_2601_ = lean_unsigned_to_nat(0);
        v___x_2602_ = l_Lean_Syntax_getArg(v_x_2597_, v___x_2601_);
        lean_dec(v_x_2597_);
        v___x_2603_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__5;
        lean_inc(v___x_2602_);
        v___x_2604_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2603_);
        if v___x_2604_ == 0 {
            let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2606_: u8 = 0;
            v___x_2605_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__7;
            lean_inc(v___x_2602_);
            v___x_2606_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2605_);
            if v___x_2606_ == 0 {
                let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2608_: u8 = 0;
                v___x_2607_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__9;
                lean_inc(v___x_2602_);
                v___x_2608_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2607_);
                if v___x_2608_ == 0 {
                    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2610_: u8 = 0;
                    v___x_2609_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__11;
                    v___x_2610_ = l_Lean_Syntax_isOfKind(v___x_2602_, v___x_2609_);
                    if v___x_2610_ == 0 {
                        let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2611_ = lean_box(0);
                        return v___x_2611_;
                    } else {
                        let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2612_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
                        return v___x_2612_;
                    }
                } else {
                    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_2602_);
                    v___x_2613_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
                    return v___x_2613_;
                }
            } else {
                let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2602_);
                v___x_2614_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
                return v___x_2614_;
            }
        } else {
            let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2602_);
            v___x_2615_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
            return v___x_2615_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(
    mut v_x_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    v___x_2642_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__1;
    lean_inc(v_x_2641_);
    v___x_2643_ = l_Lean_Syntax_isOfKind(v_x_2641_, v___x_2642_);
    if v___x_2643_ == 0 {
        let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2641_);
        v___x_2644_ = lean_box(0);
        return v___x_2644_;
    } else {
        let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: u8 = 0;
        v___x_2645_ = lean_unsigned_to_nat(0);
        v___x_2646_ = l_Lean_Syntax_getArg(v_x_2641_, v___x_2645_);
        lean_dec(v_x_2641_);
        v___x_2647_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__3;
        lean_inc(v___x_2646_);
        v___x_2648_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2647_);
        if v___x_2648_ == 0 {
            let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2650_: u8 = 0;
            v___x_2649_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__5;
            lean_inc(v___x_2646_);
            v___x_2650_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2649_);
            if v___x_2650_ == 0 {
                let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2652_: u8 = 0;
                v___x_2651_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__7;
                lean_inc(v___x_2646_);
                v___x_2652_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2651_);
                if v___x_2652_ == 0 {
                    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2654_: u8 = 0;
                    v___x_2653_ = l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind___closed__9;
                    v___x_2654_ = l_Lean_Syntax_isOfKind(v___x_2646_, v___x_2653_);
                    if v___x_2654_ == 0 {
                        let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2655_ = lean_box(0);
                        return v___x_2655_;
                    } else {
                        let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2656_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
                        return v___x_2656_;
                    }
                } else {
                    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_2646_);
                    v___x_2657_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
                    return v___x_2657_;
                }
            } else {
                let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2646_);
                v___x_2658_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
                return v___x_2658_;
            }
        } else {
            let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2646_);
            v___x_2659_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
            return v___x_2659_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(
    mut v_x_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    v___x_2686_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
    lean_inc(v_x_2685_);
    v___x_2687_ = l_Lean_Syntax_isOfKind(v_x_2685_, v___x_2686_);
    if v___x_2687_ == 0 {
        let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_2685_);
        v___x_2688_ = lean_box(0);
        return v___x_2688_;
    } else {
        let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2692_: u8 = 0;
        v___x_2689_ = lean_unsigned_to_nat(0);
        v___x_2690_ = l_Lean_Syntax_getArg(v_x_2685_, v___x_2689_);
        lean_dec(v_x_2685_);
        v___x_2691_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__3;
        lean_inc(v___x_2690_);
        v___x_2692_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2691_);
        if v___x_2692_ == 0 {
            let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2694_: u8 = 0;
            v___x_2693_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__5;
            lean_inc(v___x_2690_);
            v___x_2694_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2693_);
            if v___x_2694_ == 0 {
                let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2696_: u8 = 0;
                v___x_2695_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__7;
                lean_inc(v___x_2690_);
                v___x_2696_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2695_);
                if v___x_2696_ == 0 {
                    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2698_: u8 = 0;
                    v___x_2697_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__9;
                    v___x_2698_ = l_Lean_Syntax_isOfKind(v___x_2690_, v___x_2697_);
                    if v___x_2698_ == 0 {
                        let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2699_ = lean_box(0);
                        return v___x_2699_;
                    } else {
                        let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
                        v___x_2700_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__12;
                        return v___x_2700_;
                    }
                } else {
                    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec(v___x_2690_);
                    v___x_2701_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__13;
                    return v___x_2701_;
                }
            } else {
                let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_2690_);
                v___x_2702_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__15;
                return v___x_2702_;
            }
        } else {
            let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_2690_);
            v___x_2703_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind___closed__17;
            return v___x_2703_;
        }
    }
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(
    mut v_x_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2721_: u8 = 0;
    let mut v_unused_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2726_: u8 = 0;
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_a_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut v_unused_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut v_a_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2752_: u8 = 0;
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2710_ = l_Lean_Meta_saveState___redArg(v___y_2706_, v___y_2708_);
                if lean_obj_tag(v___x_2710_) == 0 {
                    v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
                    lean_inc(v_a_2711_);
                    lean_dec_ref_known(v___x_2710_, 1);
                    lean_inc(v___y_2708_);
                    lean_inc_ref(v___y_2707_);
                    lean_inc(v___y_2706_);
                    lean_inc_ref(v___y_2705_);
                    v_r_2712_ = lean_apply_5(
                        v_x_2704_,
                        v___y_2705_,
                        v___y_2706_,
                        v___y_2707_,
                        v___y_2708_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_2712_) == 0 {
                        v_a_2713_ = lean_ctor_get(v_r_2712_, 0);
                        lean_inc(v_a_2713_);
                        lean_dec_ref_known(v_r_2712_, 1);
                        v___x_2714_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_2711_,
                            v___y_2706_,
                            v___y_2708_,
                        );
                        lean_dec(v_a_2711_);
                        if lean_obj_tag(v___x_2714_) == 0 {
                            v_isSharedCheck_2721_ = (!lean_is_exclusive(v___x_2714_)) as u8;
                            if v_isSharedCheck_2721_ == 0 {
                                v_unused_2722_ = lean_ctor_get(v___x_2714_, 0);
                                lean_dec(v_unused_2722_);
                                v___x_2716_ = v___x_2714_;
                                v_isShared_2717_ = v_isSharedCheck_2721_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_2714_);
                                v___x_2716_ = lean_box(0);
                                v_isShared_2717_ = v_isSharedCheck_2721_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2713_);
                            v_a_2723_ = lean_ctor_get(v___x_2714_, 0);
                            v_isSharedCheck_2730_ = (!lean_is_exclusive(v___x_2714_)) as u8;
                            if v_isSharedCheck_2730_ == 0 {
                                v___x_2725_ = v___x_2714_;
                                v_isShared_2726_ = v_isSharedCheck_2730_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2723_);
                                lean_dec(v___x_2714_);
                                v___x_2725_ = lean_box(0);
                                v_isShared_2726_ = v_isSharedCheck_2730_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_2731_ = lean_ctor_get(v_r_2712_, 0);
                        lean_inc(v_a_2731_);
                        lean_dec_ref_known(v_r_2712_, 1);
                        v___x_2732_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_2711_,
                            v___y_2706_,
                            v___y_2708_,
                        );
                        lean_dec(v_a_2711_);
                        if lean_obj_tag(v___x_2732_) == 0 {
                            v_isSharedCheck_2739_ = (!lean_is_exclusive(v___x_2732_)) as u8;
                            if v_isSharedCheck_2739_ == 0 {
                                v_unused_2740_ = lean_ctor_get(v___x_2732_, 0);
                                lean_dec(v_unused_2740_);
                                v___x_2734_ = v___x_2732_;
                                v_isShared_2735_ = v_isSharedCheck_2739_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_2732_);
                                v___x_2734_ = lean_box(0);
                                v_isShared_2735_ = v_isSharedCheck_2739_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2731_);
                            v_a_2741_ = lean_ctor_get(v___x_2732_, 0);
                            v_isSharedCheck_2748_ = (!lean_is_exclusive(v___x_2732_)) as u8;
                            if v_isSharedCheck_2748_ == 0 {
                                v___x_2743_ = v___x_2732_;
                                v_isShared_2744_ = v_isSharedCheck_2748_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2741_);
                                lean_dec(v___x_2732_);
                                v___x_2743_ = lean_box(0);
                                v_isShared_2744_ = v_isSharedCheck_2748_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_x_2704_);
                    v_a_2749_ = lean_ctor_get(v___x_2710_, 0);
                    v_isSharedCheck_2756_ = (!lean_is_exclusive(v___x_2710_)) as u8;
                    if v_isSharedCheck_2756_ == 0 {
                        v___x_2751_ = v___x_2710_;
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2749_);
                        lean_dec(v___x_2710_);
                        v___x_2751_ = lean_box(0);
                        v_isShared_2752_ = v_isSharedCheck_2756_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2717_ == 0 {
                    lean_ctor_set(v___x_2716_, 0, v_a_2713_);
                    v___x_2719_ = v___x_2716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2713_);
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
                    v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
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
                    lean_ctor_set_tag(v___x_2734_, 1);
                    lean_ctor_set(v___x_2734_, 0, v_a_2731_);
                    v___x_2737_ = v___x_2734_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2731_);
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
                    v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
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
                    v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
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
    mut v_x_2757_: *mut LeanObject,
    mut v___y_2758_: *mut LeanObject,
    mut v___y_2759_: *mut LeanObject,
    mut v___y_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2763_: *mut LeanObject = core::ptr::null_mut();
    v_res_2763_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_);
    lean_dec(v___y_2761_);
    lean_dec_ref(v___y_2760_);
    lean_dec(v___y_2759_);
    lean_dec_ref(v___y_2758_);
    return v_res_2763_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(
    mut v_00_u03b1_2764_: *mut LeanObject,
    mut v_x_2765_: *mut LeanObject,
    mut v___y_2766_: *mut LeanObject,
    mut v___y_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    v___x_2771_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v_x_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
    return v___x_2771_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___boxed(
    mut v_00_u03b1_2772_: *mut LeanObject,
    mut v_x_2773_: *mut LeanObject,
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2779_: *mut LeanObject = core::ptr::null_mut();
    v_res_2779_ =
        l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0(
            v_00_u03b1_2772_,
            v_x_2773_,
            v___y_2774_,
            v___y_2775_,
            v___y_2776_,
            v___y_2777_,
        );
    lean_dec(v___y_2777_);
    lean_dec_ref(v___y_2776_);
    lean_dec(v___y_2775_);
    lean_dec_ref(v___y_2774_);
    return v_res_2779_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(
    mut v_red_2780_: u8,
    mut v_a_2781_: *mut LeanObject,
    mut v_b_2782_: *mut LeanObject,
    mut v___y_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2809_: u8 = 0;
    let mut v_trackZetaDelta_2810_: u8 = 0;
    let mut v_zetaDeltaSet_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2817_: u8 = 0;
    let mut v_inTypeClassResolution_2818_: u8 = 0;
    let mut v_cacheInferType_2819_: u8 = 0;
    let mut v_config_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u64 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: u64 = 0;
    let mut v___x_2827_: u64 = 0;
    let mut v___x_2828_: u64 = 0;
    let mut v___x_2829_: u64 = 0;
    let mut v_key_2830_: u64 = 0;
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut v_unused_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2788_ = l_Lean_Meta_Context_config(v___y_2783_);
                v_foApprox_2789_ = lean_ctor_get_uint8(v___x_2788_, 0 as u32);
                v_ctxApprox_2790_ = lean_ctor_get_uint8(v___x_2788_, 1 as u32);
                v_quasiPatternApprox_2791_ = lean_ctor_get_uint8(v___x_2788_, 2 as u32);
                v_constApprox_2792_ = lean_ctor_get_uint8(v___x_2788_, 3 as u32);
                v_isDefEqStuckEx_2793_ = lean_ctor_get_uint8(v___x_2788_, 4 as u32);
                v_unificationHints_2794_ = lean_ctor_get_uint8(v___x_2788_, 5 as u32);
                v_proofIrrelevance_2795_ = lean_ctor_get_uint8(v___x_2788_, 6 as u32);
                v_assignSyntheticOpaque_2796_ = lean_ctor_get_uint8(v___x_2788_, 7 as u32);
                v_offsetCnstrs_2797_ = lean_ctor_get_uint8(v___x_2788_, 8 as u32);
                v_etaStruct_2798_ = lean_ctor_get_uint8(v___x_2788_, 10 as u32);
                v_univApprox_2799_ = lean_ctor_get_uint8(v___x_2788_, 11 as u32);
                v_iota_2800_ = lean_ctor_get_uint8(v___x_2788_, 12 as u32);
                v_beta_2801_ = lean_ctor_get_uint8(v___x_2788_, 13 as u32);
                v_proj_2802_ = lean_ctor_get_uint8(v___x_2788_, 14 as u32);
                v_zeta_2803_ = lean_ctor_get_uint8(v___x_2788_, 15 as u32);
                v_zetaDelta_2804_ = lean_ctor_get_uint8(v___x_2788_, 16 as u32);
                v_zetaUnused_2805_ = lean_ctor_get_uint8(v___x_2788_, 17 as u32);
                v_zetaHave_2806_ = lean_ctor_get_uint8(v___x_2788_, 18 as u32);
                v_isSharedCheck_2845_ = (!lean_is_exclusive(v___x_2788_)) as u8;
                if v_isSharedCheck_2845_ == 0 {
                    v___x_2808_ = v___x_2788_;
                    v_isShared_2809_ = v_isSharedCheck_2845_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_2788_);
                    v___x_2808_ = lean_box(0);
                    v_isShared_2809_ = v_isSharedCheck_2845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_2810_ = lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2811_ = lean_ctor_get(v___y_2783_, 1);
                lean_inc(v_zetaDeltaSet_2811_);
                v_lctx_2812_ = lean_ctor_get(v___y_2783_, 2);
                lean_inc_ref(v_lctx_2812_);
                v_localInstances_2813_ = lean_ctor_get(v___y_2783_, 3);
                lean_inc_ref(v_localInstances_2813_);
                v_defEqCtx_x3f_2814_ = lean_ctor_get(v___y_2783_, 4);
                lean_inc(v_defEqCtx_x3f_2814_);
                v_synthPendingDepth_2815_ = lean_ctor_get(v___y_2783_, 5);
                lean_inc(v_synthPendingDepth_2815_);
                v_canUnfold_x3f_2816_ = lean_ctor_get(v___y_2783_, 6);
                lean_inc(v_canUnfold_x3f_2816_);
                v_univApprox_2817_ = lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2818_ = lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2819_ = lean_ctor_get_uint8(
                    v___y_2783_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2809_ == 0 {
                    v_config_2821_ = v___x_2808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 0 as u32, v_foApprox_2789_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 1 as u32, v_ctxApprox_2790_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        2 as u32,
                        v_quasiPatternApprox_2791_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 3 as u32, v_constApprox_2792_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 4 as u32, v_isDefEqStuckEx_2793_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 5 as u32, v_unificationHints_2794_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 6 as u32, v_proofIrrelevance_2795_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2844_,
                        7 as u32,
                        v_assignSyntheticOpaque_2796_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 8 as u32, v_offsetCnstrs_2797_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 10 as u32, v_etaStruct_2798_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 11 as u32, v_univApprox_2799_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 12 as u32, v_iota_2800_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 13 as u32, v_beta_2801_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 14 as u32, v_proj_2802_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 15 as u32, v_zeta_2803_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 16 as u32, v_zetaDelta_2804_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 17 as u32, v_zetaUnused_2805_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2844_, 18 as u32, v_zetaHave_2806_);
                    v_config_2821_ = v_reuseFailAlloc_2844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v_config_2821_, 9 as u32, v_red_2780_);
                v___x_2822_ = l_Lean_Meta_Context_configKey(v___y_2783_);
                v_isSharedCheck_2836_ = (!lean_is_exclusive(v___y_2783_)) as u8;
                if v_isSharedCheck_2836_ == 0 {
                    v_unused_2837_ = lean_ctor_get(v___y_2783_, 6);
                    lean_dec(v_unused_2837_);
                    v_unused_2838_ = lean_ctor_get(v___y_2783_, 5);
                    lean_dec(v_unused_2838_);
                    v_unused_2839_ = lean_ctor_get(v___y_2783_, 4);
                    lean_dec(v_unused_2839_);
                    v_unused_2840_ = lean_ctor_get(v___y_2783_, 3);
                    lean_dec(v_unused_2840_);
                    v_unused_2841_ = lean_ctor_get(v___y_2783_, 2);
                    lean_dec(v_unused_2841_);
                    v_unused_2842_ = lean_ctor_get(v___y_2783_, 1);
                    lean_dec(v_unused_2842_);
                    v_unused_2843_ = lean_ctor_get(v___y_2783_, 0);
                    lean_dec(v_unused_2843_);
                    v___x_2824_ = v___y_2783_;
                    v_isShared_2825_ = v_isSharedCheck_2836_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___y_2783_);
                    v___x_2824_ = lean_box(0);
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
                v___x_2831_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_2831_, 0, v_config_2821_);
                lean_ctor_set_uint64(
                    v___x_2831_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_2830_,
                );
                if v_isShared_2825_ == 0 {
                    lean_ctor_set(v___x_2824_, 0, v___x_2831_);
                    v___x_2833_ = v___x_2824_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2831_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 1, v_zetaDeltaSet_2811_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_lctx_2812_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 3, v_localInstances_2813_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 4, v_defEqCtx_x3f_2814_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 5, v_synthPendingDepth_2815_);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 6, v_canUnfold_x3f_2816_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_trackZetaDelta_2810_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v_univApprox_2817_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_2818_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2835_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
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
                lean_dec_ref(v___x_2833_);
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed(
    mut v_red_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
    mut v_b_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
    mut v___y_2850_: *mut LeanObject,
    mut v___y_2851_: *mut LeanObject,
    mut v___y_2852_: *mut LeanObject,
    mut v___y_2853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_red_1788__boxed_2854_: u8 = 0;
    let mut v_res_2855_: *mut LeanObject = core::ptr::null_mut();
    v_red_1788__boxed_2854_ = (lean_unbox(v_red_2846_) as u8);
    v_res_2855_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0(
        v_red_1788__boxed_2854_,
        v_a_2847_,
        v_b_2848_,
        v___y_2849_,
        v___y_2850_,
        v___y_2851_,
        v___y_2852_,
    );
    lean_dec(v___y_2852_);
    lean_dec_ref(v___y_2851_);
    lean_dec(v___y_2850_);
    return v_res_2855_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
    mut v_a_2856_: *mut LeanObject,
    mut v_b_2857_: *mut LeanObject,
    mut v_x_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
    mut v_a_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2858_) {
        0 => {
            let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2866_: u8 = 0;
            let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
            v___x_2864_ = l_Lean_Expr_consumeMData(v_a_2856_);
            lean_dec_ref(v_a_2856_);
            v___x_2865_ = l_Lean_Expr_consumeMData(v_b_2857_);
            lean_dec_ref(v_b_2857_);
            v___x_2866_ = lean_expr_eqv(v___x_2864_, v___x_2865_);
            lean_dec_ref(v___x_2865_);
            lean_dec_ref(v___x_2864_);
            v___x_2867_ = lean_box((v___x_2866_) as usize);
            v___x_2868_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_2868_, 0, v___x_2867_);
            return v___x_2868_;
        }
        1 => {
            let mut v_red_2869_: u8 = 0;
            let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_2871_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
            v_red_2869_ = lean_ctor_get_uint8(v_x_2858_, 0 as u32);
            v___x_2870_ = lean_box((v_red_2869_) as usize);
            v___f_2871_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___lam__0___boxed
                    as *mut core::ffi::c_void,
                8,
                3,
            );
            lean_closure_set(v___f_2871_, 0, v___x_2870_);
            lean_closure_set(v___f_2871_, 1, v_a_2856_);
            lean_closure_set(v___f_2871_, 2, v_b_2857_);
            v___x_2872_ = l_Lean_withoutModifyingState___at___00Lean_Elab_Tactic_GuardExpr_MatchKind_isEq_spec__0___redArg(v___f_2871_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
            return v___x_2872_;
        }
        _ => {
            let mut v___x_2873_: u8 = 0;
            let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
            v___x_2873_ = lean_expr_eqv(v_a_2856_, v_b_2857_);
            lean_dec_ref(v_b_2857_);
            lean_dec_ref(v_a_2856_);
            v___x_2874_ = lean_box((v___x_2873_) as usize);
            v___x_2875_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_2875_, 0, v___x_2874_);
            return v___x_2875_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq___boxed(
    mut v_a_2876_: *mut LeanObject,
    mut v_b_2877_: *mut LeanObject,
    mut v_x_2878_: *mut LeanObject,
    mut v_a_2879_: *mut LeanObject,
    mut v_a_2880_: *mut LeanObject,
    mut v_a_2881_: *mut LeanObject,
    mut v_a_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2884_: *mut LeanObject = core::ptr::null_mut();
    v_res_2884_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
        v_a_2876_, v_b_2877_, v_x_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_,
    );
    lean_dec(v_a_2882_);
    lean_dec_ref(v_a_2881_);
    lean_dec(v_a_2880_);
    lean_dec_ref(v_a_2879_);
    lean_dec(v_x_2878_);
    return v_res_2884_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(
    mut v_x_2892_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_2892_) {
        0 => {
            let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
            v___x_2893_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__0;
            return v___x_2893_;
        }
        1 => {
            let mut v_red_2894_: u8 = 0;
            v_red_2894_ = lean_ctor_get_uint8(v_x_2892_, 0 as u32);
            match v_red_2894_ {
                0 => {
                    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2895_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__1;
                    return v___x_2895_;
                }
                1 => {
                    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2896_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__2;
                    return v___x_2896_;
                }
                2 => {
                    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2897_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__3;
                    return v___x_2897_;
                }
                3 => {
                    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2898_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__4;
                    return v___x_2898_;
                }
                _ => {
                    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
                    v___x_2899_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__5;
                    return v___x_2899_;
                }
            }
        }
        _ => {
            let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
            v___x_2900_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___closed__6;
            return v___x_2900_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr___boxed(
    mut v_x_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2902_: *mut LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_x_2901_);
    lean_dec(v_x_2901_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(
    mut v_e_2903_: *mut LeanObject,
    mut v___y_2904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_unused_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2906_ = l_Lean_Expr_hasMVar(v_e_2903_);
                if v___x_2906_ == 0 {
                    v___x_2907_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2907_, 0, v_e_2903_);
                    return v___x_2907_;
                } else {
                    v___x_2908_ = lean_st_ref_get(v___y_2904_);
                    v_mctx_2909_ = lean_ctor_get(v___x_2908_, 0);
                    lean_inc_ref(v_mctx_2909_);
                    lean_dec(v___x_2908_);
                    v___x_2910_ = l_Lean_instantiateMVarsCore(v_mctx_2909_, v_e_2903_);
                    v_fst_2911_ = lean_ctor_get(v___x_2910_, 0);
                    lean_inc(v_fst_2911_);
                    v_snd_2912_ = lean_ctor_get(v___x_2910_, 1);
                    lean_inc(v_snd_2912_);
                    lean_dec_ref(v___x_2910_);
                    v___x_2913_ = lean_st_ref_take(v___y_2904_);
                    v_cache_2914_ = lean_ctor_get(v___x_2913_, 1);
                    v_zetaDeltaFVarIds_2915_ = lean_ctor_get(v___x_2913_, 2);
                    v_postponed_2916_ = lean_ctor_get(v___x_2913_, 3);
                    v_diag_2917_ = lean_ctor_get(v___x_2913_, 4);
                    v_isSharedCheck_2926_ = (!lean_is_exclusive(v___x_2913_)) as u8;
                    if v_isSharedCheck_2926_ == 0 {
                        v_unused_2927_ = lean_ctor_get(v___x_2913_, 0);
                        lean_dec(v_unused_2927_);
                        v___x_2919_ = v___x_2913_;
                        v_isShared_2920_ = v_isSharedCheck_2926_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2917_);
                        lean_inc(v_postponed_2916_);
                        lean_inc(v_zetaDeltaFVarIds_2915_);
                        lean_inc(v_cache_2914_);
                        lean_dec(v___x_2913_);
                        v___x_2919_ = lean_box(0);
                        v_isShared_2920_ = v_isSharedCheck_2926_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2920_ == 0 {
                    lean_ctor_set(v___x_2919_, 0, v_snd_2912_);
                    v___x_2922_ = v___x_2919_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_snd_2912_);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_cache_2914_);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_zetaDeltaFVarIds_2915_);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_postponed_2916_);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 4, v_diag_2917_);
                    v___x_2922_ = v_reuseFailAlloc_2925_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2923_ = lean_st_ref_set(v___y_2904_, v___x_2922_);
                v___x_2924_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2924_, 0, v_fst_2911_);
                return v___x_2924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg___boxed(
    mut v_e_2928_: *mut LeanObject,
    mut v___y_2929_: *mut LeanObject,
    mut v___y_2930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2931_: *mut LeanObject = core::ptr::null_mut();
    v_res_2931_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_2928_, v___y_2929_);
    lean_dec(v___y_2929_);
    return v_res_2931_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0(
    mut v_e_2932_: *mut LeanObject,
    mut v___y_2933_: *mut LeanObject,
    mut v___y_2934_: *mut LeanObject,
    mut v___y_2935_: *mut LeanObject,
    mut v___y_2936_: *mut LeanObject,
    mut v___y_2937_: *mut LeanObject,
    mut v___y_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    v___x_2940_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_e_2932_, v___y_2936_);
    return v___x_2940_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___boxed(
    mut v_e_2941_: *mut LeanObject,
    mut v___y_2942_: *mut LeanObject,
    mut v___y_2943_: *mut LeanObject,
    mut v___y_2944_: *mut LeanObject,
    mut v___y_2945_: *mut LeanObject,
    mut v___y_2946_: *mut LeanObject,
    mut v___y_2947_: *mut LeanObject,
    mut v___y_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2949_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2947_);
    lean_dec_ref(v___y_2946_);
    lean_dec(v___y_2945_);
    lean_dec_ref(v___y_2944_);
    lean_dec(v___y_2943_);
    lean_dec_ref(v___y_2942_);
    return v_res_2949_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(
    mut v_a_2950_: *mut LeanObject,
    mut v___y_2951_: *mut LeanObject,
    mut v___y_2952_: *mut LeanObject,
    mut v___y_2953_: *mut LeanObject,
    mut v___y_2954_: *mut LeanObject,
    mut v___y_2955_: *mut LeanObject,
    mut v___y_2956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2959_: *mut LeanObject,
    mut v___y_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
    mut v___y_2966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2967_: *mut LeanObject = core::ptr::null_mut();
    v_res_2967_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1___redArg(v_a_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
    lean_dec(v___y_2965_);
    lean_dec_ref(v___y_2964_);
    lean_dec(v___y_2963_);
    lean_dec_ref(v___y_2962_);
    lean_dec(v___y_2961_);
    lean_dec_ref(v___y_2960_);
    return v_res_2967_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(
    mut v_00_u03b1_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v___y_2970_: *mut LeanObject,
    mut v___y_2971_: *mut LeanObject,
    mut v___y_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
    mut v___y_2974_: *mut LeanObject,
    mut v___y_2975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2978_: *mut LeanObject,
    mut v_a_2979_: *mut LeanObject,
    mut v___y_2980_: *mut LeanObject,
    mut v___y_2981_: *mut LeanObject,
    mut v___y_2982_: *mut LeanObject,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2987_: *mut LeanObject = core::ptr::null_mut();
    v_res_2987_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__1(v_00_u03b1_2978_, v_a_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
    lean_dec(v___y_2985_);
    lean_dec_ref(v___y_2984_);
    lean_dec(v___y_2983_);
    lean_dec_ref(v___y_2982_);
    lean_dec(v___y_2981_);
    lean_dec_ref(v___y_2980_);
    return v_res_2987_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0(
    mut v_a_2988_: *mut LeanObject,
    mut v___x_2989_: *mut LeanObject,
    mut v___x_2990_: u8,
    mut v_b_2991_: *mut LeanObject,
    mut v_mk_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
    mut v___y_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: u8 = 0;
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3019_: u8 = 0;
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_a_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3027_: u8 = 0;
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3031_: u8 = 0;
    let mut v_a_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut v_a_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut v_a_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_2989_);
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
                if lean_obj_tag(v___x_3000_) == 0 {
                    v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
                    lean_inc(v_a_3001_);
                    lean_dec_ref_known(v___x_3000_, 1);
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
                    if lean_obj_tag(v___x_3002_) == 0 {
                        v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
                        lean_inc(v_a_3003_);
                        lean_dec_ref_known(v___x_3002_, 1);
                        lean_inc(v___y_2998_);
                        lean_inc_ref(v___y_2997_);
                        lean_inc(v___y_2996_);
                        lean_inc_ref(v___y_2995_);
                        lean_inc(v_a_3001_);
                        v___x_3004_ = lean_infer_type(
                            v_a_3001_,
                            v___y_2995_,
                            v___y_2996_,
                            v___y_2997_,
                            v___y_2998_,
                        );
                        if lean_obj_tag(v___x_3004_) == 0 {
                            v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
                            lean_inc(v_a_3005_);
                            lean_dec_ref_known(v___x_3004_, 1);
                            lean_inc(v___y_2998_);
                            lean_inc_ref(v___y_2997_);
                            lean_inc(v___y_2996_);
                            lean_inc_ref(v___y_2995_);
                            lean_inc(v_a_3003_);
                            v___x_3006_ = lean_infer_type(
                                v_a_3003_,
                                v___y_2995_,
                                v___y_2996_,
                                v___y_2997_,
                                v___y_2998_,
                            );
                            if lean_obj_tag(v___x_3006_) == 0 {
                                v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
                                lean_inc(v_a_3007_);
                                lean_dec_ref_known(v___x_3006_, 1);
                                v___x_3008_ = l_Lean_Meta_isExprDefEqGuarded(
                                    v_a_3005_,
                                    v_a_3007_,
                                    v___y_2995_,
                                    v___y_2996_,
                                    v___y_2997_,
                                    v___y_2998_,
                                );
                                if lean_obj_tag(v___x_3008_) == 0 {
                                    lean_dec_ref_known(v___x_3008_, 1);
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
                                    if lean_obj_tag(v___x_3010_) == 0 {
                                        lean_dec_ref_known(v___x_3010_, 1);
                                        v___x_3011_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_3001_, v___y_2996_);
                                        v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
                                        lean_inc(v_a_3012_);
                                        lean_dec_ref(v___x_3011_);
                                        v___x_3013_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_3003_, v___y_2996_);
                                        v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
                                        lean_inc(v_a_3014_);
                                        lean_dec_ref(v___x_3013_);
                                        v___x_3015_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                                            v_a_3012_,
                                            v_a_3014_,
                                            v_mk_2992_,
                                            v___y_2995_,
                                            v___y_2996_,
                                            v___y_2997_,
                                            v___y_2998_,
                                        );
                                        lean_dec(v___y_2998_);
                                        lean_dec_ref(v___y_2997_);
                                        lean_dec(v___y_2996_);
                                        lean_dec_ref(v___y_2995_);
                                        return v___x_3015_;
                                    } else {
                                        lean_dec(v_a_3003_);
                                        lean_dec(v_a_3001_);
                                        lean_dec(v___y_2998_);
                                        lean_dec_ref(v___y_2997_);
                                        lean_dec(v___y_2996_);
                                        lean_dec_ref(v___y_2995_);
                                        v_a_3016_ = lean_ctor_get(v___x_3010_, 0);
                                        v_isSharedCheck_3023_ =
                                            (!lean_is_exclusive(v___x_3010_)) as u8;
                                        if v_isSharedCheck_3023_ == 0 {
                                            v___x_3018_ = v___x_3010_;
                                            v_isShared_3019_ = v_isSharedCheck_3023_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3016_);
                                            lean_dec(v___x_3010_);
                                            v___x_3018_ = lean_box(0);
                                            v_isShared_3019_ = v_isSharedCheck_3023_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_3003_);
                                    lean_dec(v_a_3001_);
                                    lean_dec(v___y_2998_);
                                    lean_dec_ref(v___y_2997_);
                                    lean_dec(v___y_2996_);
                                    lean_dec_ref(v___y_2995_);
                                    return v___x_3008_;
                                }
                            } else {
                                lean_dec(v_a_3005_);
                                lean_dec(v_a_3003_);
                                lean_dec(v_a_3001_);
                                lean_dec(v___y_2998_);
                                lean_dec_ref(v___y_2997_);
                                lean_dec(v___y_2996_);
                                lean_dec_ref(v___y_2995_);
                                v_a_3024_ = lean_ctor_get(v___x_3006_, 0);
                                v_isSharedCheck_3031_ = (!lean_is_exclusive(v___x_3006_)) as u8;
                                if v_isSharedCheck_3031_ == 0 {
                                    v___x_3026_ = v___x_3006_;
                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_3024_);
                                    lean_dec(v___x_3006_);
                                    v___x_3026_ = lean_box(0);
                                    v_isShared_3027_ = v_isSharedCheck_3031_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3003_);
                            lean_dec(v_a_3001_);
                            lean_dec(v___y_2998_);
                            lean_dec_ref(v___y_2997_);
                            lean_dec(v___y_2996_);
                            lean_dec_ref(v___y_2995_);
                            v_a_3032_ = lean_ctor_get(v___x_3004_, 0);
                            v_isSharedCheck_3039_ = (!lean_is_exclusive(v___x_3004_)) as u8;
                            if v_isSharedCheck_3039_ == 0 {
                                v___x_3034_ = v___x_3004_;
                                v_isShared_3035_ = v_isSharedCheck_3039_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3032_);
                                lean_dec(v___x_3004_);
                                v___x_3034_ = lean_box(0);
                                v_isShared_3035_ = v_isSharedCheck_3039_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3001_);
                        lean_dec(v___y_2998_);
                        lean_dec_ref(v___y_2997_);
                        lean_dec(v___y_2996_);
                        lean_dec_ref(v___y_2995_);
                        v_a_3040_ = lean_ctor_get(v___x_3002_, 0);
                        v_isSharedCheck_3047_ = (!lean_is_exclusive(v___x_3002_)) as u8;
                        if v_isSharedCheck_3047_ == 0 {
                            v___x_3042_ = v___x_3002_;
                            v_isShared_3043_ = v_isSharedCheck_3047_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3040_);
                            lean_dec(v___x_3002_);
                            v___x_3042_ = lean_box(0);
                            v_isShared_3043_ = v_isSharedCheck_3047_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2998_);
                    lean_dec_ref(v___y_2997_);
                    lean_dec(v___y_2996_);
                    lean_dec_ref(v___y_2995_);
                    lean_dec(v_b_2991_);
                    lean_dec(v___x_2989_);
                    v_a_3048_ = lean_ctor_get(v___x_3000_, 0);
                    v_isSharedCheck_3055_ = (!lean_is_exclusive(v___x_3000_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v___x_3050_ = v___x_3000_;
                        v_isShared_3051_ = v_isSharedCheck_3055_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3048_);
                        lean_dec(v___x_3000_);
                        v___x_3050_ = lean_box(0);
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
                    v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
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
                    v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
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
                    v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
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
                    v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
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
                    v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
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
    mut v_a_3056_: *mut LeanObject,
    mut v___x_3057_: *mut LeanObject,
    mut v___x_3058_: *mut LeanObject,
    mut v_b_3059_: *mut LeanObject,
    mut v_mk_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
    mut v___y_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
    mut v___y_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1677__boxed_3068_: u8 = 0;
    let mut v_res_3069_: *mut LeanObject = core::ptr::null_mut();
    v___x_1677__boxed_3068_ = (lean_unbox(v___x_3058_) as u8);
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
    lean_dec(v___y_3062_);
    lean_dec_ref(v___y_3061_);
    lean_dec(v_mk_3060_);
    return v_res_3069_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(
    mut v_mk_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_b_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
    mut v_a_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
    mut v_a_3077_: *mut LeanObject,
    mut v_a_3078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    v___x_3080_ = lean_box(0);
    v___x_3081_ = 1;
    v___x_3082_ = lean_box((v___x_3081_) as usize);
    v___f_3083_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind___lam__0___boxed
            as *mut core::ffi::c_void,
        12,
        5,
    );
    lean_closure_set(v___f_3083_, 0, v_a_3071_);
    lean_closure_set(v___f_3083_, 1, v___x_3080_);
    lean_closure_set(v___f_3083_, 2, v___x_3082_);
    lean_closure_set(v___f_3083_, 3, v_b_3072_);
    lean_closure_set(v___f_3083_, 4, v_mk_3070_);
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
    mut v_mk_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
    mut v_b_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_a_3092_: *mut LeanObject,
    mut v_a_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3095_: *mut LeanObject = core::ptr::null_mut();
    v_res_3095_ = l_Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind(
        v_mk_3085_, v_a_3086_, v_b_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_,
        v_a_3093_,
    );
    lean_dec(v_a_3093_);
    lean_dec_ref(v_a_3092_);
    lean_dec(v_a_3091_);
    lean_dec_ref(v_a_3090_);
    lean_dec(v_a_3089_);
    lean_dec_ref(v_a_3088_);
    return v_res_3095_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    v___x_3096_ = lean_box(0);
    v___x_3097_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3098_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3098_, 0, v___x_3097_);
    lean_ctor_set(v___x_3098_, 1, v___x_3096_);
    return v___x_3098_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    v___x_3100_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
    v___x_3101_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3101_, 0, v___x_3100_);
    return v___x_3101_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___boxed(
    mut v___y_3102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3103_: *mut LeanObject = core::ptr::null_mut();
    v_res_3103_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
    return v_res_3103_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(
    mut v_00_u03b1_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    v___x_3114_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
    return v___x_3114_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___boxed(
    mut v_00_u03b1_3115_: *mut LeanObject,
    mut v___y_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
    mut v___y_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3125_: *mut LeanObject = core::ptr::null_mut();
    v_res_3125_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0(v_00_u03b1_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
    lean_dec(v___y_3123_);
    lean_dec_ref(v___y_3122_);
    lean_dec(v___y_3121_);
    lean_dec_ref(v___y_3120_);
    lean_dec(v___y_3119_);
    lean_dec_ref(v___y_3118_);
    lean_dec(v___y_3117_);
    lean_dec_ref(v___y_3116_);
    return v_res_3125_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(
    mut v_msgData_3126_: *mut LeanObject,
    mut v___y_3127_: *mut LeanObject,
    mut v___y_3128_: *mut LeanObject,
    mut v___y_3129_: *mut LeanObject,
    mut v___y_3130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    v___x_3132_ = lean_st_ref_get(v___y_3130_);
    v_env_3133_ = lean_ctor_get(v___x_3132_, 0);
    lean_inc_ref(v_env_3133_);
    lean_dec(v___x_3132_);
    v___x_3134_ = lean_st_ref_get(v___y_3128_);
    v_mctx_3135_ = lean_ctor_get(v___x_3134_, 0);
    lean_inc_ref(v_mctx_3135_);
    lean_dec(v___x_3134_);
    v_lctx_3136_ = lean_ctor_get(v___y_3127_, 2);
    v_options_3137_ = lean_ctor_get(v___y_3129_, 2);
    lean_inc_ref(v_options_3137_);
    lean_inc_ref(v_lctx_3136_);
    v___x_3138_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3138_, 0, v_env_3133_);
    lean_ctor_set(v___x_3138_, 1, v_mctx_3135_);
    lean_ctor_set(v___x_3138_, 2, v_lctx_3136_);
    lean_ctor_set(v___x_3138_, 3, v_options_3137_);
    v___x_3139_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3139_, 0, v___x_3138_);
    lean_ctor_set(v___x_3139_, 1, v_msgData_3126_);
    v___x_3140_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3140_, 0, v___x_3139_);
    return v___x_3140_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1___boxed(
    mut v_msgData_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
    mut v___y_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3147_: *mut LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msgData_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
    lean_dec(v___y_3145_);
    lean_dec_ref(v___y_3144_);
    lean_dec(v___y_3143_);
    lean_dec_ref(v___y_3142_);
    return v_res_3147_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(
    mut v_msg_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3154_ = lean_ctor_get(v___y_3151_, 5);
                v___x_3155_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
                v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
                v_isSharedCheck_3164_ = (!lean_is_exclusive(v___x_3155_)) as u8;
                if v_isSharedCheck_3164_ == 0 {
                    v___x_3158_ = v___x_3155_;
                    v_isShared_3159_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3156_);
                    lean_dec(v___x_3155_);
                    v___x_3158_ = lean_box(0);
                    v_isShared_3159_ = v_isSharedCheck_3164_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3154_);
                v___x_3160_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3160_, 0, v_ref_3154_);
                lean_ctor_set(v___x_3160_, 1, v_a_3156_);
                if v_isShared_3159_ == 0 {
                    lean_ctor_set_tag(v___x_3158_, 1);
                    lean_ctor_set(v___x_3158_, 0, v___x_3160_);
                    v___x_3162_ = v___x_3158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
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
    mut v_msg_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3171_: *mut LeanObject = core::ptr::null_mut();
    v_res_3171_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(
            v_msg_3165_,
            v___y_3166_,
            v___y_3167_,
            v___y_3168_,
            v___y_3169_,
        );
    lean_dec(v___y_3169_);
    lean_dec_ref(v___y_3168_);
    lean_dec(v___y_3167_);
    lean_dec_ref(v___y_3166_);
    return v_res_3171_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    v___x_3173_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__0;
    v___x_3174_ = l_Lean_stringToMessageData(v___x_3173_);
    return v___x_3174_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    v___x_3176_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__2;
    v___x_3177_ = l_Lean_stringToMessageData(v___x_3176_);
    return v___x_3177_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    v___x_3179_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__4;
    v___x_3180_ = l_Lean_stringToMessageData(v___x_3179_);
    return v___x_3180_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    v___x_3182_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__6;
    v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
    return v___x_3183_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0(
    mut v___x_3184_: *mut LeanObject,
    mut v_r_3185_: *mut LeanObject,
    mut v_p_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
    mut v___y_3191_: *mut LeanObject,
    mut v___y_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3202_: u8 = 0;
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut v_a_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___x_3184_) == 1 {
                    v_val_3196_ = lean_ctor_get(v___x_3184_, 0);
                    lean_inc_n(v_val_3196_, 2);
                    lean_dec_ref_known(v___x_3184_, 1);
                    lean_inc(v_p_3186_);
                    lean_inc(v_r_3185_);
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
                    if lean_obj_tag(v___x_3197_) == 0 {
                        v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
                        v_isSharedCheck_3222_ = (!lean_is_exclusive(v___x_3197_)) as u8;
                        if v_isSharedCheck_3222_ == 0 {
                            v___x_3200_ = v___x_3197_;
                            v_isShared_3201_ = v_isSharedCheck_3222_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3198_);
                            lean_dec(v___x_3197_);
                            v___x_3200_ = lean_box(0);
                            v_isShared_3201_ = v_isSharedCheck_3222_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3196_);
                        lean_dec(v_p_3186_);
                        lean_dec(v_r_3185_);
                        v_a_3223_ = lean_ctor_get(v___x_3197_, 0);
                        v_isSharedCheck_3230_ = (!lean_is_exclusive(v___x_3197_)) as u8;
                        if v_isSharedCheck_3230_ == 0 {
                            v___x_3225_ = v___x_3197_;
                            v_isShared_3226_ = v_isSharedCheck_3230_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3223_);
                            lean_dec(v___x_3197_);
                            v___x_3225_ = lean_box(0);
                            v_isShared_3226_ = v_isSharedCheck_3230_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_p_3186_);
                    lean_dec(v_r_3185_);
                    lean_dec(v___x_3184_);
                    v___x_3231_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                    return v___x_3231_;
                }
            }
            1 => {
                v___x_3202_ = (lean_unbox(v_a_3198_) as u8);
                lean_dec(v_a_3198_);
                if v___x_3202_ == 0 {
                    lean_del_object(v___x_3200_);
                    v___x_3203_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1,
                    );
                    v___x_3204_ = l_Lean_MessageData_ofSyntax(v_r_3185_);
                    v___x_3205_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3205_, 0, v___x_3203_);
                    lean_ctor_set(v___x_3205_, 1, v___x_3204_);
                    v___x_3206_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3,
                    );
                    v___x_3207_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3207_, 0, v___x_3205_);
                    lean_ctor_set(v___x_3207_, 1, v___x_3206_);
                    v___x_3208_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_3196_);
                    lean_dec(v_val_3196_);
                    v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
                    v___x_3210_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3210_, 0, v___x_3207_);
                    lean_ctor_set(v___x_3210_, 1, v___x_3209_);
                    v___x_3211_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5,
                    );
                    v___x_3212_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3212_, 0, v___x_3210_);
                    lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                    v___x_3213_ = l_Lean_MessageData_ofSyntax(v_p_3186_);
                    v___x_3214_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3214_, 0, v___x_3212_);
                    lean_ctor_set(v___x_3214_, 1, v___x_3213_);
                    v___x_3215_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7,
                    );
                    v___x_3216_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3216_, 0, v___x_3214_);
                    lean_ctor_set(v___x_3216_, 1, v___x_3215_);
                    v___x_3217_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3216_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
                    return v___x_3217_;
                } else {
                    lean_dec(v_val_3196_);
                    lean_dec(v_p_3186_);
                    lean_dec(v_r_3185_);
                    v___x_3218_ = lean_box(0);
                    if v_isShared_3201_ == 0 {
                        lean_ctor_set(v___x_3200_, 0, v___x_3218_);
                        v___x_3220_ = v___x_3200_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
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
                    v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3223_);
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
    mut v___x_3232_: *mut LeanObject,
    mut v_r_3233_: *mut LeanObject,
    mut v_p_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
    mut v___y_3240_: *mut LeanObject,
    mut v___y_3241_: *mut LeanObject,
    mut v___y_3242_: *mut LeanObject,
    mut v___y_3243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3244_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3242_);
    lean_dec_ref(v___y_3241_);
    lean_dec(v___y_3240_);
    lean_dec_ref(v___y_3239_);
    lean_dec(v___y_3238_);
    lean_dec_ref(v___y_3237_);
    lean_dec(v___y_3236_);
    lean_dec_ref(v___y_3235_);
    return v_res_3244_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(
    mut v_x_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
    mut v_a_3263_: *mut LeanObject,
    mut v_a_3264_: *mut LeanObject,
    mut v_a_3265_: *mut LeanObject,
    mut v_a_3266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: u8 = 0;
    v___x_3268_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
    lean_inc(v_x_3258_);
    v___x_3269_ = l_Lean_Syntax_isOfKind(v_x_3258_, v___x_3268_);
    if v___x_3269_ == 0 {
        let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3271_: u8 = 0;
        v___x_3270_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__4;
        lean_inc(v_x_3258_);
        v___x_3271_ = l_Lean_Syntax_isOfKind(v_x_3258_, v___x_3270_);
        if v___x_3271_ == 0 {
            let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_3258_);
            v___x_3272_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
            return v___x_3272_;
        } else {
            let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
            let mut v_eq_3274_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3276_: u8 = 0;
            v___x_3273_ = lean_unsigned_to_nat(2);
            v_eq_3274_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3273_);
            v___x_3275_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
            lean_inc(v_eq_3274_);
            v___x_3276_ = l_Lean_Syntax_isOfKind(v_eq_3274_, v___x_3275_);
            if v___x_3276_ == 0 {
                let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_eq_3274_);
                lean_dec(v_x_3258_);
                v___x_3277_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                return v___x_3277_;
            } else {
                let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
                let mut v_r_3279_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
                let mut v_p_3281_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
                let mut v___y_3283_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
                v___x_3278_ = lean_unsigned_to_nat(1);
                v_r_3279_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3278_);
                v___x_3280_ = lean_unsigned_to_nat(3);
                v_p_3281_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3280_);
                lean_dec(v_x_3258_);
                v___x_3282_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_3274_);
                v___y_3283_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    3,
                );
                lean_closure_set(v___y_3283_, 0, v___x_3282_);
                lean_closure_set(v___y_3283_, 1, v_r_3279_);
                lean_closure_set(v___y_3283_, 2, v_p_3281_);
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
        let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
        let mut v_eq_3286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3288_: u8 = 0;
        v___x_3285_ = lean_unsigned_to_nat(2);
        v_eq_3286_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3285_);
        v___x_3287_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
        lean_inc(v_eq_3286_);
        v___x_3288_ = l_Lean_Syntax_isOfKind(v_eq_3286_, v___x_3287_);
        if v___x_3288_ == 0 {
            let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_eq_3286_);
            lean_dec(v_x_3258_);
            v___x_3289_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
            return v___x_3289_;
        } else {
            let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_3291_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_3293_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
            let mut v___y_3295_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
            v___x_3290_ = lean_unsigned_to_nat(1);
            v_r_3291_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3290_);
            v___x_3292_ = lean_unsigned_to_nat(3);
            v_p_3293_ = l_Lean_Syntax_getArg(v_x_3258_, v___x_3292_);
            lean_dec(v_x_3258_);
            v___x_3294_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_3286_);
            v___y_3295_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___boxed
                    as *mut core::ffi::c_void,
                12,
                3,
            );
            lean_closure_set(v___y_3295_, 0, v___x_3294_);
            lean_closure_set(v___y_3295_, 1, v_r_3291_);
            lean_closure_set(v___y_3295_, 2, v_p_3293_);
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
    mut v_x_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_a_3299_: *mut LeanObject,
    mut v_a_3300_: *mut LeanObject,
    mut v_a_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
    mut v_a_3304_: *mut LeanObject,
    mut v_a_3305_: *mut LeanObject,
    mut v_a_3306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3307_: *mut LeanObject = core::ptr::null_mut();
    v_res_3307_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(
        v_x_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_,
        v_a_3305_,
    );
    lean_dec(v_a_3305_);
    lean_dec_ref(v_a_3304_);
    lean_dec(v_a_3303_);
    lean_dec_ref(v_a_3302_);
    lean_dec(v_a_3301_);
    lean_dec_ref(v_a_3300_);
    lean_dec(v_a_3299_);
    lean_dec_ref(v_a_3298_);
    return v_res_3307_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1(
    mut v_00_u03b1_3308_: *mut LeanObject,
    mut v_msg_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
    mut v___y_3312_: *mut LeanObject,
    mut v___y_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
    mut v___y_3315_: *mut LeanObject,
    mut v___y_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_3320_: *mut LeanObject,
    mut v_msg_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3331_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3329_);
    lean_dec_ref(v___y_3328_);
    lean_dec(v___y_3327_);
    lean_dec_ref(v___y_3326_);
    lean_dec(v___y_3325_);
    lean_dec_ref(v___y_3324_);
    lean_dec(v___y_3323_);
    lean_dec_ref(v___y_3322_);
    return v_res_3331_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1()
-> *mut LeanObject {
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v___x_3342_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3343_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___closed__2;
    v___x_3344_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3;
    v___x_3345_ = lean_alloc_closure(
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
    mut v_a_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3348_: *mut LeanObject = core::ptr::null_mut();
    v_res_3348_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
    return v_res_3348_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3()
-> *mut LeanObject {
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    v___x_3375_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1___closed__3;
    v___x_3376_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___closed__6;
    v___x_3377_ = l_Lean_addBuiltinDeclarationRanges(v___x_3375_, v___x_3376_);
    return v___x_3377_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3___boxed(
    mut v_a_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3379_: *mut LeanObject = core::ptr::null_mut();
    v_res_3379_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
    return v_res_3379_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(
    mut v_a_3380_: *mut LeanObject,
    mut v_a_3381_: *mut LeanObject,
    mut v_a_3382_: *mut LeanObject,
    mut v_a_3383_: *mut LeanObject,
    mut v_a_3384_: *mut LeanObject,
    mut v_a_3385_: *mut LeanObject,
    mut v_a_3386_: *mut LeanObject,
    mut v_a_3387_: *mut LeanObject,
    mut v_a_3388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    v___x_3390_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr(
        v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_,
        v_a_3388_,
    );
    return v___x_3390_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___boxed(
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
    mut v_a_3393_: *mut LeanObject,
    mut v_a_3394_: *mut LeanObject,
    mut v_a_3395_: *mut LeanObject,
    mut v_a_3396_: *mut LeanObject,
    mut v_a_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
    mut v_a_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3401_: *mut LeanObject = core::ptr::null_mut();
    v_res_3401_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv(
        v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_,
        v_a_3399_,
    );
    lean_dec(v_a_3399_);
    lean_dec_ref(v_a_3398_);
    lean_dec(v_a_3397_);
    lean_dec_ref(v_a_3396_);
    lean_dec(v_a_3395_);
    lean_dec_ref(v_a_3394_);
    lean_dec(v_a_3393_);
    lean_dec_ref(v_a_3392_);
    return v_res_3401_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1()
-> *mut LeanObject {
    let mut v___f_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    v___f_3410_ = lean_alloc_closure(
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
    mut v_a_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3416_: *mut LeanObject = core::ptr::null_mut();
    v_res_3416_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
    return v_res_3416_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3()
-> *mut LeanObject {
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    v___x_3443_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1___closed__1;
    v___x_3444_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___closed__6;
    v___x_3445_ = l_Lean_addBuiltinDeclarationRanges(v___x_3443_, v___x_3444_);
    return v___x_3445_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3___boxed(
    mut v_a_3446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3447_: *mut LeanObject = core::ptr::null_mut();
    v_res_3447_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
    return v_res_3447_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(
    mut v_e_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3451_: u8 = 0;
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_unused_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3451_ = l_Lean_Expr_hasMVar(v_e_3448_);
                if v___x_3451_ == 0 {
                    v___x_3452_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3452_, 0, v_e_3448_);
                    return v___x_3452_;
                } else {
                    v___x_3453_ = lean_st_ref_get(v___y_3449_);
                    v_mctx_3454_ = lean_ctor_get(v___x_3453_, 0);
                    lean_inc_ref(v_mctx_3454_);
                    lean_dec(v___x_3453_);
                    v___x_3455_ = l_Lean_instantiateMVarsCore(v_mctx_3454_, v_e_3448_);
                    v_fst_3456_ = lean_ctor_get(v___x_3455_, 0);
                    lean_inc(v_fst_3456_);
                    v_snd_3457_ = lean_ctor_get(v___x_3455_, 1);
                    lean_inc(v_snd_3457_);
                    lean_dec_ref(v___x_3455_);
                    v___x_3458_ = lean_st_ref_take(v___y_3449_);
                    v_cache_3459_ = lean_ctor_get(v___x_3458_, 1);
                    v_zetaDeltaFVarIds_3460_ = lean_ctor_get(v___x_3458_, 2);
                    v_postponed_3461_ = lean_ctor_get(v___x_3458_, 3);
                    v_diag_3462_ = lean_ctor_get(v___x_3458_, 4);
                    v_isSharedCheck_3471_ = (!lean_is_exclusive(v___x_3458_)) as u8;
                    if v_isSharedCheck_3471_ == 0 {
                        v_unused_3472_ = lean_ctor_get(v___x_3458_, 0);
                        lean_dec(v_unused_3472_);
                        v___x_3464_ = v___x_3458_;
                        v_isShared_3465_ = v_isSharedCheck_3471_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3462_);
                        lean_inc(v_postponed_3461_);
                        lean_inc(v_zetaDeltaFVarIds_3460_);
                        lean_inc(v_cache_3459_);
                        lean_dec(v___x_3458_);
                        v___x_3464_ = lean_box(0);
                        v_isShared_3465_ = v_isSharedCheck_3471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3465_ == 0 {
                    lean_ctor_set(v___x_3464_, 0, v_snd_3457_);
                    v___x_3467_ = v___x_3464_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_snd_3457_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_cache_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_zetaDeltaFVarIds_3460_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_postponed_3461_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_diag_3462_);
                    v___x_3467_ = v_reuseFailAlloc_3470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3468_ = lean_st_ref_set(v___y_3449_, v___x_3467_);
                v___x_3469_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3469_, 0, v_fst_3456_);
                return v___x_3469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg___boxed(
    mut v_e_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3476_: *mut LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_3473_, v___y_3474_);
    lean_dec(v___y_3474_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0(
    mut v_e_3477_: *mut LeanObject,
    mut v___y_3478_: *mut LeanObject,
    mut v___y_3479_: *mut LeanObject,
    mut v___y_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    v___x_3487_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_e_3477_, v___y_3483_);
    return v___x_3487_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___boxed(
    mut v_e_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3498_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_3496_);
    lean_dec_ref(v___y_3495_);
    lean_dec(v___y_3494_);
    lean_dec_ref(v___y_3493_);
    lean_dec(v___y_3492_);
    lean_dec_ref(v___y_3491_);
    lean_dec(v___y_3490_);
    lean_dec_ref(v___y_3489_);
    return v_res_3498_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    v___x_3500_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__0;
    v___x_3501_ = l_Lean_stringToMessageData(v___x_3500_);
    return v___x_3501_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    v___x_3503_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__2;
    v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
    return v___x_3504_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0(
    mut v_getTgt_3505_: *mut LeanObject,
    mut v_r_3506_: *mut LeanObject,
    mut v_eq_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_a_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3568_: u8 = 0;
    let mut v_reuseFailAlloc_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3573_: u8 = 0;
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3577_: u8 = 0;
    let mut v_isSharedCheck_3578_: u8 = 0;
    let mut v_a_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3582_: u8 = 0;
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3515_);
                lean_inc_ref(v___y_3514_);
                lean_inc(v___y_3513_);
                lean_inc_ref(v___y_3512_);
                lean_inc(v___y_3511_);
                lean_inc_ref(v___y_3510_);
                lean_inc(v___y_3509_);
                lean_inc_ref(v___y_3508_);
                v___x_3517_ = lean_apply_9(
                    v_getTgt_3505_,
                    v___y_3508_,
                    v___y_3509_,
                    v___y_3510_,
                    v___y_3511_,
                    v___y_3512_,
                    v___y_3513_,
                    v___y_3514_,
                    v___y_3515_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3517_) == 0 {
                    v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
                    lean_inc(v_a_3518_);
                    lean_dec_ref_known(v___x_3517_, 1);
                    v___x_3519_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_a_3518_, v___y_3513_);
                    v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
                    v_isSharedCheck_3578_ = (!lean_is_exclusive(v___x_3519_)) as u8;
                    if v_isSharedCheck_3578_ == 0 {
                        v___x_3522_ = v___x_3519_;
                        v_isShared_3523_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3520_);
                        lean_dec(v___x_3519_);
                        v___x_3522_ = lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3578_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_3515_);
                    lean_dec_ref(v___y_3514_);
                    lean_dec(v___y_3513_);
                    lean_dec_ref(v___y_3512_);
                    lean_dec(v___y_3511_);
                    lean_dec_ref(v___y_3510_);
                    lean_dec(v___y_3509_);
                    lean_dec_ref(v___y_3508_);
                    lean_dec(v_eq_3507_);
                    lean_dec(v_r_3506_);
                    v_a_3579_ = lean_ctor_get(v___x_3517_, 0);
                    v_isSharedCheck_3586_ = (!lean_is_exclusive(v___x_3517_)) as u8;
                    if v_isSharedCheck_3586_ == 0 {
                        v___x_3581_ = v___x_3517_;
                        v_isShared_3582_ = v_isSharedCheck_3586_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_3579_);
                        lean_dec(v___x_3517_);
                        v___x_3581_ = lean_box(0);
                        v_isShared_3582_ = v_isSharedCheck_3586_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_3515_);
                lean_inc_ref(v___y_3514_);
                lean_inc(v___y_3513_);
                lean_inc_ref(v___y_3512_);
                lean_inc(v_a_3520_);
                v___x_3524_ = lean_infer_type(
                    v_a_3520_,
                    v___y_3512_,
                    v___y_3513_,
                    v___y_3514_,
                    v___y_3515_,
                );
                if lean_obj_tag(v___x_3524_) == 0 {
                    v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
                    lean_inc(v_a_3525_);
                    lean_dec_ref_known(v___x_3524_, 1);
                    if v_isShared_3523_ == 0 {
                        lean_ctor_set_tag(v___x_3522_, 1);
                        lean_ctor_set(v___x_3522_, 0, v_a_3525_);
                        v___x_3527_ = v___x_3522_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3525_);
                        v___x_3527_ = v_reuseFailAlloc_3569_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3522_);
                    lean_dec(v_a_3520_);
                    lean_dec(v___y_3515_);
                    lean_dec_ref(v___y_3514_);
                    lean_dec(v___y_3513_);
                    lean_dec_ref(v___y_3512_);
                    lean_dec(v___y_3511_);
                    lean_dec_ref(v___y_3510_);
                    lean_dec(v___y_3509_);
                    lean_dec_ref(v___y_3508_);
                    lean_dec(v_eq_3507_);
                    lean_dec(v_r_3506_);
                    v_a_3570_ = lean_ctor_get(v___x_3524_, 0);
                    v_isSharedCheck_3577_ = (!lean_is_exclusive(v___x_3524_)) as u8;
                    if v_isSharedCheck_3577_ == 0 {
                        v___x_3572_ = v___x_3524_;
                        v_isShared_3573_ = v_isSharedCheck_3577_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3570_);
                        lean_dec(v___x_3524_);
                        v___x_3572_ = lean_box(0);
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
                lean_dec(v___y_3511_);
                lean_dec_ref(v___y_3510_);
                lean_dec(v___y_3509_);
                lean_dec_ref(v___y_3508_);
                if lean_obj_tag(v___x_3529_) == 0 {
                    v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
                    lean_inc(v_a_3530_);
                    lean_dec_ref_known(v___x_3529_, 1);
                    v___x_3531_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_3507_);
                    if lean_obj_tag(v___x_3531_) == 1 {
                        v_val_3532_ = lean_ctor_get(v___x_3531_, 0);
                        lean_inc(v_val_3532_);
                        lean_dec_ref_known(v___x_3531_, 1);
                        lean_inc(v_a_3520_);
                        lean_inc(v_a_3530_);
                        v___x_3533_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                            v_a_3530_,
                            v_a_3520_,
                            v_val_3532_,
                            v___y_3512_,
                            v___y_3513_,
                            v___y_3514_,
                            v___y_3515_,
                        );
                        lean_dec(v_val_3532_);
                        if lean_obj_tag(v___x_3533_) == 0 {
                            v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
                            v_isSharedCheck_3551_ = (!lean_is_exclusive(v___x_3533_)) as u8;
                            if v_isSharedCheck_3551_ == 0 {
                                v___x_3536_ = v___x_3533_;
                                v_isShared_3537_ = v_isSharedCheck_3551_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_3534_);
                                lean_dec(v___x_3533_);
                                v___x_3536_ = lean_box(0);
                                v_isShared_3537_ = v_isSharedCheck_3551_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3530_);
                            lean_dec(v_a_3520_);
                            lean_dec(v___y_3515_);
                            lean_dec_ref(v___y_3514_);
                            lean_dec(v___y_3513_);
                            lean_dec_ref(v___y_3512_);
                            v_a_3552_ = lean_ctor_get(v___x_3533_, 0);
                            v_isSharedCheck_3559_ = (!lean_is_exclusive(v___x_3533_)) as u8;
                            if v_isSharedCheck_3559_ == 0 {
                                v___x_3554_ = v___x_3533_;
                                v_isShared_3555_ = v_isSharedCheck_3559_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3552_);
                                lean_dec(v___x_3533_);
                                v___x_3554_ = lean_box(0);
                                v_isShared_3555_ = v_isSharedCheck_3559_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3531_);
                        lean_dec(v_a_3530_);
                        lean_dec(v_a_3520_);
                        lean_dec(v___y_3515_);
                        lean_dec_ref(v___y_3514_);
                        lean_dec(v___y_3513_);
                        lean_dec_ref(v___y_3512_);
                        v___x_3560_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_3560_;
                    }
                } else {
                    lean_dec(v_a_3520_);
                    lean_dec(v___y_3515_);
                    lean_dec_ref(v___y_3514_);
                    lean_dec(v___y_3513_);
                    lean_dec_ref(v___y_3512_);
                    lean_dec(v_eq_3507_);
                    v_a_3561_ = lean_ctor_get(v___x_3529_, 0);
                    v_isSharedCheck_3568_ = (!lean_is_exclusive(v___x_3529_)) as u8;
                    if v_isSharedCheck_3568_ == 0 {
                        v___x_3563_ = v___x_3529_;
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3561_);
                        lean_dec(v___x_3529_);
                        v___x_3563_ = lean_box(0);
                        v_isShared_3564_ = v_isSharedCheck_3568_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3538_ = (lean_unbox(v_a_3534_) as u8);
                lean_dec(v_a_3534_);
                if v___x_3538_ == 0 {
                    lean_del_object(v___x_3536_);
                    v___x_3539_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__1,
                    );
                    v___x_3540_ = l_Lean_indentExpr(v_a_3520_);
                    v___x_3541_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3541_, 0, v___x_3539_);
                    lean_ctor_set(v___x_3541_, 1, v___x_3540_);
                    v___x_3542_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___closed__3,
                    );
                    v___x_3543_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3543_, 0, v___x_3541_);
                    lean_ctor_set(v___x_3543_, 1, v___x_3542_);
                    v___x_3544_ = l_Lean_indentExpr(v_a_3530_);
                    v___x_3545_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3545_, 0, v___x_3543_);
                    lean_ctor_set(v___x_3545_, 1, v___x_3544_);
                    v___x_3546_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3545_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
                    lean_dec(v___y_3515_);
                    lean_dec_ref(v___y_3514_);
                    lean_dec(v___y_3513_);
                    lean_dec_ref(v___y_3512_);
                    return v___x_3546_;
                } else {
                    lean_dec(v_a_3530_);
                    lean_dec(v_a_3520_);
                    lean_dec(v___y_3515_);
                    lean_dec_ref(v___y_3514_);
                    lean_dec(v___y_3513_);
                    lean_dec_ref(v___y_3512_);
                    v___x_3547_ = lean_box(0);
                    if v_isShared_3537_ == 0 {
                        lean_ctor_set(v___x_3536_, 0, v___x_3547_);
                        v___x_3549_ = v___x_3536_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3550_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
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
                    v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
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
                    v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
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
                    v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
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
                    v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
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
    mut v_getTgt_3587_: *mut LeanObject,
    mut v_r_3588_: *mut LeanObject,
    mut v_eq_3589_: *mut LeanObject,
    mut v___y_3590_: *mut LeanObject,
    mut v___y_3591_: *mut LeanObject,
    mut v___y_3592_: *mut LeanObject,
    mut v___y_3593_: *mut LeanObject,
    mut v___y_3594_: *mut LeanObject,
    mut v___y_3595_: *mut LeanObject,
    mut v___y_3596_: *mut LeanObject,
    mut v___y_3597_: *mut LeanObject,
    mut v___y_3598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3599_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_3614_: *mut LeanObject,
    mut v_a_3615_: *mut LeanObject,
    mut v_a_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
    mut v_a_3618_: *mut LeanObject,
    mut v_a_3619_: *mut LeanObject,
    mut v_a_3620_: *mut LeanObject,
    mut v_a_3621_: *mut LeanObject,
    mut v_a_3622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eq_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getTgt_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eq_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eq_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3638_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
                lean_inc(v_x_3614_);
                v___x_3639_ = l_Lean_Syntax_isOfKind(v_x_3614_, v___x_3638_);
                if v___x_3639_ == 0 {
                    v___x_3640_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__3;
                    lean_inc(v_x_3614_);
                    v___x_3641_ = l_Lean_Syntax_isOfKind(v_x_3614_, v___x_3640_);
                    if v___x_3641_ == 0 {
                        lean_dec(v_x_3614_);
                        v___x_3642_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_3642_;
                    } else {
                        v___x_3643_ = lean_unsigned_to_nat(1);
                        v_eq_3644_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3643_);
                        v___x_3645_ = lean_unsigned_to_nat(2);
                        v___x_3646_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3645_);
                        lean_dec(v_x_3614_);
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
                    v___x_3648_ = lean_unsigned_to_nat(1);
                    v_eq_3649_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3648_);
                    v___x_3650_ = lean_unsigned_to_nat(2);
                    v___x_3651_ = l_Lean_Syntax_getArg(v_x_3614_, v___x_3650_);
                    lean_dec(v_x_3614_);
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
                lean_inc_ref(v_getTgt_3627_);
                v___f_3636_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___lam__0___boxed
                        as *mut core::ffi::c_void,
                    12,
                    3,
                );
                lean_closure_set(v___f_3636_, 0, v_getTgt_3627_);
                lean_closure_set(v___f_3636_, 1, v_r_3626_);
                lean_closure_set(v___f_3636_, 2, v_eq_3625_);
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
    mut v_x_3653_: *mut LeanObject,
    mut v_a_3654_: *mut LeanObject,
    mut v_a_3655_: *mut LeanObject,
    mut v_a_3656_: *mut LeanObject,
    mut v_a_3657_: *mut LeanObject,
    mut v_a_3658_: *mut LeanObject,
    mut v_a_3659_: *mut LeanObject,
    mut v_a_3660_: *mut LeanObject,
    mut v_a_3661_: *mut LeanObject,
    mut v_a_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3663_: *mut LeanObject = core::ptr::null_mut();
    v_res_3663_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(
        v_x_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_,
        v_a_3661_,
    );
    lean_dec(v_a_3661_);
    lean_dec_ref(v_a_3660_);
    lean_dec(v_a_3659_);
    lean_dec_ref(v_a_3658_);
    lean_dec(v_a_3657_);
    lean_dec_ref(v_a_3656_);
    lean_dec(v_a_3655_);
    lean_dec_ref(v_a_3654_);
    return v_res_3663_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1()
-> *mut LeanObject {
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    v___x_3672_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3673_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget___closed__1;
    v___x_3674_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1;
    v___x_3675_ = lean_alloc_closure(
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
    mut v_a_3677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3678_: *mut LeanObject = core::ptr::null_mut();
    v_res_3678_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
    return v_res_3678_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3()
-> *mut LeanObject {
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    v___x_3705_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1___closed__1;
    v___x_3706_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___closed__6;
    v___x_3707_ = l_Lean_addBuiltinDeclarationRanges(v___x_3705_, v___x_3706_);
    return v___x_3707_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3___boxed(
    mut v_a_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3709_: *mut LeanObject = core::ptr::null_mut();
    v_res_3709_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
    return v_res_3709_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(
    mut v_a_3710_: *mut LeanObject,
    mut v_a_3711_: *mut LeanObject,
    mut v_a_3712_: *mut LeanObject,
    mut v_a_3713_: *mut LeanObject,
    mut v_a_3714_: *mut LeanObject,
    mut v_a_3715_: *mut LeanObject,
    mut v_a_3716_: *mut LeanObject,
    mut v_a_3717_: *mut LeanObject,
    mut v_a_3718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    v___x_3720_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTarget(
        v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_,
        v_a_3718_,
    );
    return v___x_3720_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___boxed(
    mut v_a_3721_: *mut LeanObject,
    mut v_a_3722_: *mut LeanObject,
    mut v_a_3723_: *mut LeanObject,
    mut v_a_3724_: *mut LeanObject,
    mut v_a_3725_: *mut LeanObject,
    mut v_a_3726_: *mut LeanObject,
    mut v_a_3727_: *mut LeanObject,
    mut v_a_3728_: *mut LeanObject,
    mut v_a_3729_: *mut LeanObject,
    mut v_a_3730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3731_: *mut LeanObject = core::ptr::null_mut();
    v_res_3731_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv(
        v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_,
        v_a_3729_,
    );
    lean_dec(v_a_3729_);
    lean_dec_ref(v_a_3728_);
    lean_dec(v_a_3727_);
    lean_dec_ref(v_a_3726_);
    lean_dec(v_a_3725_);
    lean_dec_ref(v_a_3724_);
    lean_dec(v_a_3723_);
    lean_dec_ref(v_a_3722_);
    return v_res_3731_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1()
-> *mut LeanObject {
    let mut v___f_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    v___f_3740_ = lean_alloc_closure(
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
    mut v_a_3745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3746_: *mut LeanObject = core::ptr::null_mut();
    v_res_3746_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
    return v_res_3746_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3()
-> *mut LeanObject {
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    v___x_3773_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1___closed__1;
    v___x_3774_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___closed__6;
    v___x_3775_ = l_Lean_addBuiltinDeclarationRanges(v___x_3773_, v___x_3774_);
    return v___x_3775_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3___boxed(
    mut v_a_3776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3777_: *mut LeanObject = core::ptr::null_mut();
    v_res_3777_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
    return v_res_3777_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__0;
    v___x_3780_ = l_Lean_stringToMessageData(v___x_3779_);
    return v___x_3780_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    v___x_3782_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__2;
    v___x_3783_ = l_Lean_stringToMessageData(v___x_3782_);
    return v___x_3783_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3785_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__4;
    v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
    return v___x_3786_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    v___x_3788_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__6;
    v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
    return v___x_3789_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    v___x_3791_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__8;
    v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
    return v___x_3792_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11()
-> *mut LeanObject {
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    v___x_3794_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__10;
    v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
    return v___x_3795_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13()
-> *mut LeanObject {
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    v___x_3797_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__12;
    v___x_3798_ = l_Lean_stringToMessageData(v___x_3797_);
    return v___x_3798_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__14;
    v___x_3801_ = l_Lean_stringToMessageData(v___x_3800_);
    return v___x_3801_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0(
    mut v___x_3802_: *mut LeanObject,
    mut v___x_3803_: u8,
    mut v_val_3804_: *mut LeanObject,
    mut v_eq_3805_: *mut LeanObject,
    mut v_c_3806_: *mut LeanObject,
    mut v_ty_3807_: *mut LeanObject,
    mut v___y_3808_: *mut LeanObject,
    mut v___y_3809_: *mut LeanObject,
    mut v___y_3810_: *mut LeanObject,
    mut v___y_3811_: *mut LeanObject,
    mut v___y_3812_: *mut LeanObject,
    mut v___y_3813_: *mut LeanObject,
    mut v___y_3814_: *mut LeanObject,
    mut v___y_3815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3862_: u8 = 0;
    let mut v___x_3863_: u8 = 0;
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3880_: u8 = 0;
    let mut v_a_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3888_: u8 = 0;
    let mut v_a_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_reuseFailAlloc_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecl_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3942_: u8 = 0;
    let mut v_a_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3946_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3950_: u8 = 0;
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3965_: u8 = 0;
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3969_: u8 = 0;
    let mut v_val_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_3802_);
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
                if lean_obj_tag(v___x_3952_) == 0 {
                    v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
                    lean_inc(v_a_3953_);
                    lean_dec_ref_known(v___x_3952_, 1);
                    v_lctx_3954_ = lean_ctor_get(v___y_3812_, 2);
                    lean_inc_ref(v_lctx_3954_);
                    v___x_3955_ = lean_local_ctx_find(v_lctx_3954_, v_a_3953_);
                    if lean_obj_tag(v___x_3955_) == 0 {
                        lean_dec(v_ty_3807_);
                        lean_dec(v_c_3806_);
                        lean_dec(v_eq_3805_);
                        lean_dec(v_val_3804_);
                        v___x_3956_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                        );
                        v___x_3957_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                        v___x_3958_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3958_, 0, v___x_3956_);
                        lean_ctor_set(v___x_3958_, 1, v___x_3957_);
                        v___x_3959_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
                        v___x_3960_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3960_, 0, v___x_3958_);
                        lean_ctor_set(v___x_3960_, 1, v___x_3959_);
                        v___x_3961_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3960_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
                        lean_dec_ref(v___y_3812_);
                        v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
                        v_isSharedCheck_3969_ = (!lean_is_exclusive(v___x_3961_)) as u8;
                        if v_isSharedCheck_3969_ == 0 {
                            v___x_3964_ = v___x_3961_;
                            v_isShared_3965_ = v_isSharedCheck_3969_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3962_);
                            lean_dec(v___x_3961_);
                            v___x_3964_ = lean_box(0);
                            v_isShared_3965_ = v_isSharedCheck_3969_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v_val_3970_ = lean_ctor_get(v___x_3955_, 0);
                        lean_inc(v_val_3970_);
                        lean_dec_ref_known(v___x_3955_, 1);
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
                    lean_dec_ref(v___y_3812_);
                    lean_dec(v_ty_3807_);
                    lean_dec(v_c_3806_);
                    lean_dec(v_eq_3805_);
                    lean_dec(v_val_3804_);
                    lean_dec(v___x_3802_);
                    v_a_3971_ = lean_ctor_get(v___x_3952_, 0);
                    v_isSharedCheck_3978_ = (!lean_is_exclusive(v___x_3952_)) as u8;
                    if v_isSharedCheck_3978_ == 0 {
                        v___x_3973_ = v___x_3952_;
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3971_);
                        lean_dec(v___x_3952_);
                        v___x_3973_ = lean_box(0);
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3827_ = l_Lean_LocalDecl_value_x3f(v___y_3818_, v___x_3803_);
                if lean_obj_tag(v___x_3827_) == 0 {
                    lean_dec_ref(v___y_3818_);
                    lean_dec(v_eq_3805_);
                    if lean_obj_tag(v_val_3804_) == 0 {
                        lean_dec_ref(v___y_3823_);
                        lean_dec(v___x_3802_);
                        v___x_3828_ = lean_box(0);
                        v___x_3829_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3829_, 0, v___x_3828_);
                        return v___x_3829_;
                    } else {
                        lean_dec_ref_known(v_val_3804_, 1);
                        v___x_3830_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_3831_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                        v___x_3832_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3832_, 0, v___x_3830_);
                        lean_ctor_set(v___x_3832_, 1, v___x_3831_);
                        v___x_3833_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1,
                        );
                        v___x_3834_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3834_, 0, v___x_3832_);
                        lean_ctor_set(v___x_3834_, 1, v___x_3833_);
                        v___x_3835_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3834_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
                        lean_dec_ref(v___y_3823_);
                        return v___x_3835_;
                    }
                } else {
                    if lean_obj_tag(v_val_3804_) == 0 {
                        lean_dec_ref_known(v___x_3827_, 1);
                        lean_dec_ref(v___y_3818_);
                        lean_dec(v_eq_3805_);
                        v___x_3836_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_3837_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                        v___x_3838_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3838_, 0, v___x_3836_);
                        lean_ctor_set(v___x_3838_, 1, v___x_3837_);
                        v___x_3839_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3,
                        );
                        v___x_3840_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3840_, 0, v___x_3838_);
                        lean_ctor_set(v___x_3840_, 1, v___x_3839_);
                        v___x_3841_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3840_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
                        lean_dec_ref(v___y_3823_);
                        return v___x_3841_;
                    } else {
                        if lean_obj_tag(v_eq_3805_) == 0 {
                            lean_dec_ref_known(v_val_3804_, 1);
                            lean_dec_ref_known(v___x_3827_, 1);
                            lean_dec_ref(v___y_3823_);
                            lean_dec_ref(v___y_3818_);
                            lean_dec(v___x_3802_);
                            v___x_3842_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_3842_;
                        } else {
                            v_val_3843_ = lean_ctor_get(v___x_3827_, 0);
                            lean_inc(v_val_3843_);
                            lean_dec_ref_known(v___x_3827_, 1);
                            v_val_3844_ = lean_ctor_get(v_val_3804_, 0);
                            lean_inc(v_val_3844_);
                            lean_dec_ref_known(v_val_3804_, 1);
                            v_val_3845_ = lean_ctor_get(v_eq_3805_, 0);
                            lean_inc(v_val_3845_);
                            lean_dec_ref_known(v_eq_3805_, 1);
                            v___x_3846_ =
                                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_3845_);
                            if lean_obj_tag(v___x_3846_) == 1 {
                                v_val_3847_ = lean_ctor_get(v___x_3846_, 0);
                                v_isSharedCheck_3898_ = (!lean_is_exclusive(v___x_3846_)) as u8;
                                if v_isSharedCheck_3898_ == 0 {
                                    v___x_3849_ = v___x_3846_;
                                    v_isShared_3850_ = v_isSharedCheck_3898_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_val_3847_);
                                    lean_dec(v___x_3846_);
                                    v___x_3849_ = lean_box(0);
                                    v_isShared_3850_ = v_isSharedCheck_3898_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_3846_);
                                lean_dec(v_val_3844_);
                                lean_dec(v_val_3843_);
                                lean_dec_ref(v___y_3823_);
                                lean_dec_ref(v___y_3818_);
                                lean_dec(v___x_3802_);
                                v___x_3899_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                                return v___x_3899_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3851_ = l_Lean_LocalDecl_type(v___y_3818_);
                lean_dec_ref(v___y_3818_);
                if v_isShared_3850_ == 0 {
                    lean_ctor_set(v___x_3849_, 0, v___x_3851_);
                    v___x_3853_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3851_);
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
                if lean_obj_tag(v___x_3854_) == 0 {
                    v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
                    lean_inc_n(v_a_3855_, 2);
                    lean_dec_ref_known(v___x_3854_, 1);
                    v___x_3856_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_3843_, v___y_3824_);
                    v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
                    lean_inc_n(v_a_3857_, 2);
                    lean_dec_ref(v___x_3856_);
                    v___x_3858_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                        v_a_3855_,
                        v_a_3857_,
                        v_val_3847_,
                        v___y_3823_,
                        v___y_3824_,
                        v___y_3825_,
                        v___y_3826_,
                    );
                    lean_dec(v_val_3847_);
                    if lean_obj_tag(v___x_3858_) == 0 {
                        v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
                        v_isSharedCheck_3880_ = (!lean_is_exclusive(v___x_3858_)) as u8;
                        if v_isSharedCheck_3880_ == 0 {
                            v___x_3861_ = v___x_3858_;
                            v_isShared_3862_ = v_isSharedCheck_3880_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3859_);
                            lean_dec(v___x_3858_);
                            v___x_3861_ = lean_box(0);
                            v_isShared_3862_ = v_isSharedCheck_3880_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3857_);
                        lean_dec(v_a_3855_);
                        lean_dec_ref(v___y_3823_);
                        lean_dec(v___x_3802_);
                        v_a_3881_ = lean_ctor_get(v___x_3858_, 0);
                        v_isSharedCheck_3888_ = (!lean_is_exclusive(v___x_3858_)) as u8;
                        if v_isSharedCheck_3888_ == 0 {
                            v___x_3883_ = v___x_3858_;
                            v_isShared_3884_ = v_isSharedCheck_3888_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3881_);
                            lean_dec(v___x_3858_);
                            v___x_3883_ = lean_box(0);
                            v_isShared_3884_ = v_isSharedCheck_3888_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_3847_);
                    lean_dec(v_val_3843_);
                    lean_dec_ref(v___y_3823_);
                    lean_dec(v___x_3802_);
                    v_a_3889_ = lean_ctor_get(v___x_3854_, 0);
                    v_isSharedCheck_3896_ = (!lean_is_exclusive(v___x_3854_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3891_ = v___x_3854_;
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3889_);
                        lean_dec(v___x_3854_);
                        v___x_3891_ = lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3863_ = (lean_unbox(v_a_3859_) as u8);
                lean_dec(v_a_3859_);
                if v___x_3863_ == 0 {
                    lean_del_object(v___x_3861_);
                    v___x_3864_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                    );
                    v___x_3865_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                    v___x_3866_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3866_, 0, v___x_3864_);
                    lean_ctor_set(v___x_3866_, 1, v___x_3865_);
                    v___x_3867_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7,
                    );
                    v___x_3868_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3868_, 0, v___x_3866_);
                    lean_ctor_set(v___x_3868_, 1, v___x_3867_);
                    v___x_3869_ = l_Lean_indentExpr(v_a_3857_);
                    v___x_3870_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3870_, 0, v___x_3868_);
                    lean_ctor_set(v___x_3870_, 1, v___x_3869_);
                    v___x_3871_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9,
                    );
                    v___x_3872_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3872_, 0, v___x_3870_);
                    lean_ctor_set(v___x_3872_, 1, v___x_3871_);
                    v___x_3873_ = l_Lean_indentExpr(v_a_3855_);
                    v___x_3874_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3874_, 0, v___x_3872_);
                    lean_ctor_set(v___x_3874_, 1, v___x_3873_);
                    v___x_3875_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3874_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
                    lean_dec_ref(v___y_3823_);
                    return v___x_3875_;
                } else {
                    lean_dec(v_a_3857_);
                    lean_dec(v_a_3855_);
                    lean_dec_ref(v___y_3823_);
                    lean_dec(v___x_3802_);
                    v___x_3876_ = lean_box(0);
                    if v_isShared_3862_ == 0 {
                        lean_ctor_set(v___x_3861_, 0, v___x_3876_);
                        v___x_3878_ = v___x_3861_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
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
                    v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
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
                    v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3894_;
            }
            10 => {
                if lean_obj_tag(v_c_3806_) == 1 {
                    if lean_obj_tag(v_ty_3807_) == 1 {
                        v_val_3910_ = lean_ctor_get(v_c_3806_, 0);
                        lean_inc(v_val_3910_);
                        lean_dec_ref_known(v_c_3806_, 1);
                        v_val_3911_ = lean_ctor_get(v_ty_3807_, 0);
                        lean_inc(v_val_3911_);
                        lean_dec_ref_known(v_ty_3807_, 1);
                        v___x_3912_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_3910_);
                        if lean_obj_tag(v___x_3912_) == 1 {
                            v_val_3913_ = lean_ctor_get(v___x_3912_, 0);
                            lean_inc(v_val_3913_);
                            lean_dec_ref_known(v___x_3912_, 1);
                            v___x_3914_ = lean_box(0);
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
                            if lean_obj_tag(v___x_3915_) == 0 {
                                v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
                                lean_inc_n(v_a_3916_, 2);
                                lean_dec_ref_known(v___x_3915_, 1);
                                v___x_3917_ = l_Lean_LocalDecl_type(v_lDecl_3901_);
                                v___x_3918_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_3917_, v___y_3907_);
                                v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
                                lean_inc_n(v_a_3919_, 2);
                                lean_dec_ref(v___x_3918_);
                                v___x_3920_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                                    v_a_3916_,
                                    v_a_3919_,
                                    v_val_3913_,
                                    v___y_3906_,
                                    v___y_3907_,
                                    v___y_3908_,
                                    v___y_3909_,
                                );
                                lean_dec(v_val_3913_);
                                if lean_obj_tag(v___x_3920_) == 0 {
                                    v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
                                    lean_inc(v_a_3921_);
                                    lean_dec_ref_known(v___x_3920_, 1);
                                    v___x_3922_ = (lean_unbox(v_a_3921_) as u8);
                                    lean_dec(v_a_3921_);
                                    if v___x_3922_ == 0 {
                                        lean_dec_ref(v_lDecl_3901_);
                                        lean_dec(v_eq_3805_);
                                        lean_dec(v_val_3804_);
                                        v___x_3923_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
                                        v___x_3924_ = l_Lean_MessageData_ofSyntax(v___x_3802_);
                                        v___x_3925_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_3925_, 0, v___x_3923_);
                                        lean_ctor_set(v___x_3925_, 1, v___x_3924_);
                                        v___x_3926_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
                                        v___x_3927_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_3927_, 0, v___x_3925_);
                                        lean_ctor_set(v___x_3927_, 1, v___x_3926_);
                                        v___x_3928_ = l_Lean_indentExpr(v_a_3919_);
                                        v___x_3929_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_3929_, 0, v___x_3927_);
                                        lean_ctor_set(v___x_3929_, 1, v___x_3928_);
                                        v___x_3930_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
                                        v___x_3931_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_3931_, 0, v___x_3929_);
                                        lean_ctor_set(v___x_3931_, 1, v___x_3930_);
                                        v___x_3932_ = l_Lean_indentExpr(v_a_3916_);
                                        v___x_3933_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_3933_, 0, v___x_3931_);
                                        lean_ctor_set(v___x_3933_, 1, v___x_3932_);
                                        v___x_3934_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_3933_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
                                        lean_dec_ref(v___y_3906_);
                                        return v___x_3934_;
                                    } else {
                                        lean_dec(v_a_3919_);
                                        lean_dec(v_a_3916_);
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
                                    lean_dec(v_a_3919_);
                                    lean_dec(v_a_3916_);
                                    lean_dec_ref(v___y_3906_);
                                    lean_dec_ref(v_lDecl_3901_);
                                    lean_dec(v_eq_3805_);
                                    lean_dec(v_val_3804_);
                                    lean_dec(v___x_3802_);
                                    v_a_3935_ = lean_ctor_get(v___x_3920_, 0);
                                    v_isSharedCheck_3942_ = (!lean_is_exclusive(v___x_3920_)) as u8;
                                    if v_isSharedCheck_3942_ == 0 {
                                        v___x_3937_ = v___x_3920_;
                                        v_isShared_3938_ = v_isSharedCheck_3942_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3935_);
                                        lean_dec(v___x_3920_);
                                        v___x_3937_ = lean_box(0);
                                        v_isShared_3938_ = v_isSharedCheck_3942_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_3913_);
                                lean_dec_ref(v___y_3906_);
                                lean_dec_ref(v_lDecl_3901_);
                                lean_dec(v_eq_3805_);
                                lean_dec(v_val_3804_);
                                lean_dec(v___x_3802_);
                                v_a_3943_ = lean_ctor_get(v___x_3915_, 0);
                                v_isSharedCheck_3950_ = (!lean_is_exclusive(v___x_3915_)) as u8;
                                if v_isSharedCheck_3950_ == 0 {
                                    v___x_3945_ = v___x_3915_;
                                    v_isShared_3946_ = v_isSharedCheck_3950_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_3943_);
                                    lean_dec(v___x_3915_);
                                    v___x_3945_ = lean_box(0);
                                    v_isShared_3946_ = v_isSharedCheck_3950_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_3912_);
                            lean_dec(v_val_3911_);
                            lean_dec_ref(v___y_3906_);
                            lean_dec_ref(v_lDecl_3901_);
                            lean_dec(v_eq_3805_);
                            lean_dec(v_val_3804_);
                            lean_dec(v___x_3802_);
                            v___x_3951_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_3951_;
                        }
                    } else {
                        lean_dec_ref_known(v_c_3806_, 1);
                        lean_dec(v_ty_3807_);
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
                    lean_dec(v_ty_3807_);
                    lean_dec(v_c_3806_);
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
                    v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
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
                    v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
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
                    v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
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
                    v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
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
    mut v___x_3979_: *mut LeanObject,
    mut v___x_3980_: *mut LeanObject,
    mut v_val_3981_: *mut LeanObject,
    mut v_eq_3982_: *mut LeanObject,
    mut v_c_3983_: *mut LeanObject,
    mut v_ty_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_14521__boxed_3994_: u8 = 0;
    let mut v_res_3995_: *mut LeanObject = core::ptr::null_mut();
    v___x_14521__boxed_3994_ = (lean_unbox(v___x_3980_) as u8);
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
    lean_dec(v___y_3992_);
    lean_dec_ref(v___y_3991_);
    lean_dec(v___y_3990_);
    lean_dec(v___y_3988_);
    lean_dec_ref(v___y_3987_);
    lean_dec(v___y_3986_);
    lean_dec_ref(v___y_3985_);
    return v_res_3995_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1(
    mut v___x_3996_: *mut LeanObject,
    mut v_val_3997_: *mut LeanObject,
    mut v_eq_3998_: *mut LeanObject,
    mut v_c_3999_: *mut LeanObject,
    mut v_ty_4000_: *mut LeanObject,
    mut v___y_4001_: *mut LeanObject,
    mut v___y_4002_: *mut LeanObject,
    mut v___y_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
    mut v___y_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: u8 = 0;
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v___x_4057_: u8 = 0;
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4074_: u8 = 0;
    let mut v_a_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4082_: u8 = 0;
    let mut v_a_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4090_: u8 = 0;
    let mut v_reuseFailAlloc_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecl_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: u8 = 0;
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: u8 = 0;
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4137_: u8 = 0;
    let mut v_a_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4141_: u8 = 0;
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4145_: u8 = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_val_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_3996_);
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
                if lean_obj_tag(v___x_4147_) == 0 {
                    v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
                    lean_inc(v_a_4148_);
                    lean_dec_ref_known(v___x_4147_, 1);
                    v_lctx_4149_ = lean_ctor_get(v___y_4005_, 2);
                    lean_inc_ref(v_lctx_4149_);
                    v___x_4150_ = lean_local_ctx_find(v_lctx_4149_, v_a_4148_);
                    if lean_obj_tag(v___x_4150_) == 0 {
                        lean_dec(v_ty_4000_);
                        lean_dec(v_c_3999_);
                        lean_dec(v_eq_3998_);
                        lean_dec(v_val_3997_);
                        v___x_4151_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                        );
                        v___x_4152_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                        v___x_4153_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4153_, 0, v___x_4151_);
                        lean_ctor_set(v___x_4153_, 1, v___x_4152_);
                        v___x_4154_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__15);
                        v___x_4155_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4155_, 0, v___x_4153_);
                        lean_ctor_set(v___x_4155_, 1, v___x_4154_);
                        v___x_4156_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4155_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
                        lean_dec_ref(v___y_4005_);
                        v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
                        v_isSharedCheck_4164_ = (!lean_is_exclusive(v___x_4156_)) as u8;
                        if v_isSharedCheck_4164_ == 0 {
                            v___x_4159_ = v___x_4156_;
                            v_isShared_4160_ = v_isSharedCheck_4164_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_4157_);
                            lean_dec(v___x_4156_);
                            v___x_4159_ = lean_box(0);
                            v_isShared_4160_ = v_isSharedCheck_4164_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v_val_4165_ = lean_ctor_get(v___x_4150_, 0);
                        lean_inc(v_val_4165_);
                        lean_dec_ref_known(v___x_4150_, 1);
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
                    lean_dec_ref(v___y_4005_);
                    lean_dec(v_ty_4000_);
                    lean_dec(v_c_3999_);
                    lean_dec(v_eq_3998_);
                    lean_dec(v_val_3997_);
                    lean_dec(v___x_3996_);
                    v_a_4166_ = lean_ctor_get(v___x_4147_, 0);
                    v_isSharedCheck_4173_ = (!lean_is_exclusive(v___x_4147_)) as u8;
                    if v_isSharedCheck_4173_ == 0 {
                        v___x_4168_ = v___x_4147_;
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_4166_);
                        lean_dec(v___x_4147_);
                        v___x_4168_ = lean_box(0);
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4020_ = 0;
                v___x_4021_ = l_Lean_LocalDecl_value_x3f(v___y_4011_, v___x_4020_);
                if lean_obj_tag(v___x_4021_) == 0 {
                    lean_dec_ref(v___y_4011_);
                    lean_dec(v_eq_3998_);
                    if lean_obj_tag(v_val_3997_) == 0 {
                        lean_dec_ref(v___y_4016_);
                        lean_dec(v___x_3996_);
                        v___x_4022_ = lean_box(0);
                        v___x_4023_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4023_, 0, v___x_4022_);
                        return v___x_4023_;
                    } else {
                        lean_dec_ref_known(v_val_3997_, 1);
                        v___x_4024_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_4025_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                        v___x_4026_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4026_, 0, v___x_4024_);
                        lean_ctor_set(v___x_4026_, 1, v___x_4025_);
                        v___x_4027_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__1,
                        );
                        v___x_4028_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4028_, 0, v___x_4026_);
                        lean_ctor_set(v___x_4028_, 1, v___x_4027_);
                        v___x_4029_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4028_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
                        lean_dec_ref(v___y_4016_);
                        return v___x_4029_;
                    }
                } else {
                    if lean_obj_tag(v_val_3997_) == 0 {
                        lean_dec_ref_known(v___x_4021_, 1);
                        lean_dec_ref(v___y_4011_);
                        lean_dec(v_eq_3998_);
                        v___x_4030_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7);
                        v___x_4031_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                        v___x_4032_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4032_, 0, v___x_4030_);
                        lean_ctor_set(v___x_4032_, 1, v___x_4031_);
                        v___x_4033_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__3,
                        );
                        v___x_4034_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4034_, 0, v___x_4032_);
                        lean_ctor_set(v___x_4034_, 1, v___x_4033_);
                        v___x_4035_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4034_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
                        lean_dec_ref(v___y_4016_);
                        return v___x_4035_;
                    } else {
                        if lean_obj_tag(v_eq_3998_) == 0 {
                            lean_dec_ref_known(v_val_3997_, 1);
                            lean_dec_ref_known(v___x_4021_, 1);
                            lean_dec_ref(v___y_4016_);
                            lean_dec_ref(v___y_4011_);
                            lean_dec(v___x_3996_);
                            v___x_4036_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_4036_;
                        } else {
                            v_val_4037_ = lean_ctor_get(v___x_4021_, 0);
                            lean_inc(v_val_4037_);
                            lean_dec_ref_known(v___x_4021_, 1);
                            v_val_4038_ = lean_ctor_get(v_val_3997_, 0);
                            lean_inc(v_val_4038_);
                            lean_dec_ref_known(v_val_3997_, 1);
                            v_val_4039_ = lean_ctor_get(v_eq_3998_, 0);
                            lean_inc(v_val_4039_);
                            lean_dec_ref_known(v_eq_3998_, 1);
                            v___x_4040_ =
                                l_Lean_Elab_Tactic_GuardExpr_colonEq_toMatchKind(v_val_4039_);
                            if lean_obj_tag(v___x_4040_) == 1 {
                                v_val_4041_ = lean_ctor_get(v___x_4040_, 0);
                                v_isSharedCheck_4092_ = (!lean_is_exclusive(v___x_4040_)) as u8;
                                if v_isSharedCheck_4092_ == 0 {
                                    v___x_4043_ = v___x_4040_;
                                    v_isShared_4044_ = v_isSharedCheck_4092_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_val_4041_);
                                    lean_dec(v___x_4040_);
                                    v___x_4043_ = lean_box(0);
                                    v_isShared_4044_ = v_isSharedCheck_4092_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4040_);
                                lean_dec(v_val_4038_);
                                lean_dec(v_val_4037_);
                                lean_dec_ref(v___y_4016_);
                                lean_dec_ref(v___y_4011_);
                                lean_dec(v___x_3996_);
                                v___x_4093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                                return v___x_4093_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4045_ = l_Lean_LocalDecl_type(v___y_4011_);
                lean_dec_ref(v___y_4011_);
                if v_isShared_4044_ == 0 {
                    lean_ctor_set(v___x_4043_, 0, v___x_4045_);
                    v___x_4047_ = v___x_4043_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4045_);
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
                if lean_obj_tag(v___x_4048_) == 0 {
                    v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
                    lean_inc_n(v_a_4049_, 2);
                    lean_dec_ref_known(v___x_4048_, 1);
                    v___x_4050_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v_val_4037_, v___y_4017_);
                    v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
                    lean_inc_n(v_a_4051_, 2);
                    lean_dec_ref(v___x_4050_);
                    v___x_4052_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                        v_a_4049_,
                        v_a_4051_,
                        v_val_4041_,
                        v___y_4016_,
                        v___y_4017_,
                        v___y_4018_,
                        v___y_4019_,
                    );
                    lean_dec(v_val_4041_);
                    if lean_obj_tag(v___x_4052_) == 0 {
                        v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
                        v_isSharedCheck_4074_ = (!lean_is_exclusive(v___x_4052_)) as u8;
                        if v_isSharedCheck_4074_ == 0 {
                            v___x_4055_ = v___x_4052_;
                            v_isShared_4056_ = v_isSharedCheck_4074_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4053_);
                            lean_dec(v___x_4052_);
                            v___x_4055_ = lean_box(0);
                            v_isShared_4056_ = v_isSharedCheck_4074_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4051_);
                        lean_dec(v_a_4049_);
                        lean_dec_ref(v___y_4016_);
                        lean_dec(v___x_3996_);
                        v_a_4075_ = lean_ctor_get(v___x_4052_, 0);
                        v_isSharedCheck_4082_ = (!lean_is_exclusive(v___x_4052_)) as u8;
                        if v_isSharedCheck_4082_ == 0 {
                            v___x_4077_ = v___x_4052_;
                            v_isShared_4078_ = v_isSharedCheck_4082_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4075_);
                            lean_dec(v___x_4052_);
                            v___x_4077_ = lean_box(0);
                            v_isShared_4078_ = v_isSharedCheck_4082_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_val_4041_);
                    lean_dec(v_val_4037_);
                    lean_dec_ref(v___y_4016_);
                    lean_dec(v___x_3996_);
                    v_a_4083_ = lean_ctor_get(v___x_4048_, 0);
                    v_isSharedCheck_4090_ = (!lean_is_exclusive(v___x_4048_)) as u8;
                    if v_isSharedCheck_4090_ == 0 {
                        v___x_4085_ = v___x_4048_;
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4083_);
                        lean_dec(v___x_4048_);
                        v___x_4085_ = lean_box(0);
                        v_isShared_4086_ = v_isSharedCheck_4090_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_4057_ = (lean_unbox(v_a_4053_) as u8);
                lean_dec(v_a_4053_);
                if v___x_4057_ == 0 {
                    lean_del_object(v___x_4055_);
                    v___x_4058_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5,
                    );
                    v___x_4059_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                    v___x_4060_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4060_, 0, v___x_4058_);
                    lean_ctor_set(v___x_4060_, 1, v___x_4059_);
                    v___x_4061_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__7,
                    );
                    v___x_4062_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4062_, 0, v___x_4060_);
                    lean_ctor_set(v___x_4062_, 1, v___x_4061_);
                    v___x_4063_ = l_Lean_indentExpr(v_a_4051_);
                    v___x_4064_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4064_, 0, v___x_4062_);
                    lean_ctor_set(v___x_4064_, 1, v___x_4063_);
                    v___x_4065_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__9,
                    );
                    v___x_4066_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4066_, 0, v___x_4064_);
                    lean_ctor_set(v___x_4066_, 1, v___x_4065_);
                    v___x_4067_ = l_Lean_indentExpr(v_a_4049_);
                    v___x_4068_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4068_, 0, v___x_4066_);
                    lean_ctor_set(v___x_4068_, 1, v___x_4067_);
                    v___x_4069_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4068_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
                    lean_dec_ref(v___y_4016_);
                    return v___x_4069_;
                } else {
                    lean_dec(v_a_4051_);
                    lean_dec(v_a_4049_);
                    lean_dec_ref(v___y_4016_);
                    lean_dec(v___x_3996_);
                    v___x_4070_ = lean_box(0);
                    if v_isShared_4056_ == 0 {
                        lean_ctor_set(v___x_4055_, 0, v___x_4070_);
                        v___x_4072_ = v___x_4055_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4070_);
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
                    v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
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
                    v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
                    v___x_4088_ = v_reuseFailAlloc_4089_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4088_;
            }
            10 => {
                if lean_obj_tag(v_c_3999_) == 1 {
                    if lean_obj_tag(v_ty_4000_) == 1 {
                        v_val_4104_ = lean_ctor_get(v_c_3999_, 0);
                        lean_inc(v_val_4104_);
                        lean_dec_ref_known(v_c_3999_, 1);
                        v_val_4105_ = lean_ctor_get(v_ty_4000_, 0);
                        lean_inc(v_val_4105_);
                        lean_dec_ref_known(v_ty_4000_, 1);
                        v___x_4106_ = l_Lean_Elab_Tactic_GuardExpr_colon_toMatchKind(v_val_4104_);
                        if lean_obj_tag(v___x_4106_) == 1 {
                            v_val_4107_ = lean_ctor_get(v___x_4106_, 0);
                            lean_inc(v_val_4107_);
                            lean_dec_ref_known(v___x_4106_, 1);
                            v___x_4108_ = lean_box(0);
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
                            if lean_obj_tag(v___x_4110_) == 0 {
                                v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
                                lean_inc_n(v_a_4111_, 2);
                                lean_dec_ref_known(v___x_4110_, 1);
                                v___x_4112_ = l_Lean_LocalDecl_type(v_lDecl_4095_);
                                v___x_4113_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_evalGuardTarget_spec__0___redArg(v___x_4112_, v___y_4101_);
                                v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
                                lean_inc_n(v_a_4114_, 2);
                                lean_dec_ref(v___x_4113_);
                                v___x_4115_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_isEq(
                                    v_a_4111_,
                                    v_a_4114_,
                                    v_val_4107_,
                                    v___y_4100_,
                                    v___y_4101_,
                                    v___y_4102_,
                                    v___y_4103_,
                                );
                                lean_dec(v_val_4107_);
                                if lean_obj_tag(v___x_4115_) == 0 {
                                    v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
                                    lean_inc(v_a_4116_);
                                    lean_dec_ref_known(v___x_4115_, 1);
                                    v___x_4117_ = (lean_unbox(v_a_4116_) as u8);
                                    lean_dec(v_a_4116_);
                                    if v___x_4117_ == 0 {
                                        lean_dec_ref(v_lDecl_4095_);
                                        lean_dec(v_eq_3998_);
                                        lean_dec(v_val_3997_);
                                        v___x_4118_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__5);
                                        v___x_4119_ = l_Lean_MessageData_ofSyntax(v___x_3996_);
                                        v___x_4120_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4120_, 0, v___x_4118_);
                                        lean_ctor_set(v___x_4120_, 1, v___x_4119_);
                                        v___x_4121_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__11);
                                        v___x_4122_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4122_, 0, v___x_4120_);
                                        lean_ctor_set(v___x_4122_, 1, v___x_4121_);
                                        v___x_4123_ = l_Lean_indentExpr(v_a_4114_);
                                        v___x_4124_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4124_, 0, v___x_4122_);
                                        lean_ctor_set(v___x_4124_, 1, v___x_4123_);
                                        v___x_4125_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13_once), _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___closed__13);
                                        v___x_4126_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4126_, 0, v___x_4124_);
                                        lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                                        v___x_4127_ = l_Lean_indentExpr(v_a_4111_);
                                        v___x_4128_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4128_, 0, v___x_4126_);
                                        lean_ctor_set(v___x_4128_, 1, v___x_4127_);
                                        v___x_4129_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1___redArg(v___x_4128_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
                                        lean_dec_ref(v___y_4100_);
                                        return v___x_4129_;
                                    } else {
                                        lean_dec(v_a_4114_);
                                        lean_dec(v_a_4111_);
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
                                    lean_dec(v_a_4114_);
                                    lean_dec(v_a_4111_);
                                    lean_dec_ref(v___y_4100_);
                                    lean_dec_ref(v_lDecl_4095_);
                                    lean_dec(v_eq_3998_);
                                    lean_dec(v_val_3997_);
                                    lean_dec(v___x_3996_);
                                    v_a_4130_ = lean_ctor_get(v___x_4115_, 0);
                                    v_isSharedCheck_4137_ = (!lean_is_exclusive(v___x_4115_)) as u8;
                                    if v_isSharedCheck_4137_ == 0 {
                                        v___x_4132_ = v___x_4115_;
                                        v_isShared_4133_ = v_isSharedCheck_4137_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4130_);
                                        lean_dec(v___x_4115_);
                                        v___x_4132_ = lean_box(0);
                                        v_isShared_4133_ = v_isSharedCheck_4137_;
                                        state = 11;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_val_4107_);
                                lean_dec_ref(v___y_4100_);
                                lean_dec_ref(v_lDecl_4095_);
                                lean_dec(v_eq_3998_);
                                lean_dec(v_val_3997_);
                                lean_dec(v___x_3996_);
                                v_a_4138_ = lean_ctor_get(v___x_4110_, 0);
                                v_isSharedCheck_4145_ = (!lean_is_exclusive(v___x_4110_)) as u8;
                                if v_isSharedCheck_4145_ == 0 {
                                    v___x_4140_ = v___x_4110_;
                                    v_isShared_4141_ = v_isSharedCheck_4145_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_4138_);
                                    lean_dec(v___x_4110_);
                                    v___x_4140_ = lean_box(0);
                                    v_isShared_4141_ = v_isSharedCheck_4145_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4106_);
                            lean_dec(v_val_4105_);
                            lean_dec_ref(v___y_4100_);
                            lean_dec_ref(v_lDecl_4095_);
                            lean_dec(v_eq_3998_);
                            lean_dec(v_val_3997_);
                            lean_dec(v___x_3996_);
                            v___x_4146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_4146_;
                        }
                    } else {
                        lean_dec_ref_known(v_c_3999_, 1);
                        lean_dec(v_ty_4000_);
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
                    lean_dec(v_ty_4000_);
                    lean_dec(v_c_3999_);
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
                    v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
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
                    v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
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
                    v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
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
                    v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
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
    mut v___x_4174_: *mut LeanObject,
    mut v_val_4175_: *mut LeanObject,
    mut v_eq_4176_: *mut LeanObject,
    mut v_c_4177_: *mut LeanObject,
    mut v_ty_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4188_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4186_);
    lean_dec_ref(v___y_4185_);
    lean_dec(v___y_4184_);
    lean_dec(v___y_4182_);
    lean_dec_ref(v___y_4181_);
    lean_dec(v___y_4180_);
    lean_dec_ref(v___y_4179_);
    return v_res_4188_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(
    mut v_x_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
    mut v_a_4205_: *mut LeanObject,
    mut v_a_4206_: *mut LeanObject,
    mut v_a_4207_: *mut LeanObject,
    mut v_a_4208_: *mut LeanObject,
    mut v_a_4209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: u8 = 0;
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: u8 = 0;
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eq_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: u8 = 0;
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eq_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: u8 = 0;
    let mut v___x_4259_: u8 = 0;
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eq_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: u8 = 0;
    let mut v___x_4299_: u8 = 0;
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eq_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: u8 = 0;
    let mut v___x_4308_: u8 = 0;
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4211_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
                lean_inc(v_x_4201_);
                v___x_4212_ = l_Lean_Syntax_isOfKind(v_x_4201_, v___x_4211_);
                if v___x_4212_ == 0 {
                    v___x_4213_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__3;
                    lean_inc(v_x_4201_);
                    v___x_4214_ = l_Lean_Syntax_isOfKind(v_x_4201_, v___x_4213_);
                    if v___x_4214_ == 0 {
                        lean_dec(v_x_4201_);
                        v___x_4215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_4215_;
                    } else {
                        v___x_4216_ = lean_unsigned_to_nat(0);
                        v___x_4217_ = lean_unsigned_to_nat(1);
                        v___x_4218_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4217_);
                        v___x_4235_ = lean_unsigned_to_nat(2);
                        v___x_4257_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4235_);
                        v___x_4258_ = l_Lean_Syntax_isNone(v___x_4257_);
                        if v___x_4258_ == 0 {
                            lean_inc(v___x_4257_);
                            v___x_4259_ = l_Lean_Syntax_matchesNull(v___x_4257_, v___x_4235_);
                            if v___x_4259_ == 0 {
                                lean_dec(v___x_4257_);
                                lean_dec(v___x_4218_);
                                lean_dec(v_x_4201_);
                                v___x_4260_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                                return v___x_4260_;
                            } else {
                                v_c_4261_ = l_Lean_Syntax_getArg(v___x_4257_, v___x_4216_);
                                v_ty_4262_ = l_Lean_Syntax_getArg(v___x_4257_, v___x_4217_);
                                lean_dec(v___x_4257_);
                                v___x_4263_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4263_, 0, v_c_4261_);
                                v___x_4264_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_4264_, 0, v_ty_4262_);
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
                            lean_dec(v___x_4257_);
                            v___x_4265_ = lean_box(0);
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
                    v___x_4266_ = lean_unsigned_to_nat(0);
                    v___x_4267_ = lean_unsigned_to_nat(1);
                    v___x_4268_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4267_);
                    v___x_4284_ = lean_unsigned_to_nat(2);
                    v___x_4306_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4284_);
                    v___x_4307_ = l_Lean_Syntax_isNone(v___x_4306_);
                    if v___x_4307_ == 0 {
                        lean_inc(v___x_4306_);
                        v___x_4308_ = l_Lean_Syntax_matchesNull(v___x_4306_, v___x_4284_);
                        if v___x_4308_ == 0 {
                            lean_dec(v___x_4306_);
                            lean_dec(v___x_4268_);
                            lean_dec(v_x_4201_);
                            v___x_4309_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                            return v___x_4309_;
                        } else {
                            v_c_4310_ = l_Lean_Syntax_getArg(v___x_4306_, v___x_4266_);
                            v_ty_4311_ = l_Lean_Syntax_getArg(v___x_4306_, v___x_4267_);
                            lean_dec(v___x_4306_);
                            v___x_4312_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4312_, 0, v_c_4310_);
                            v___x_4313_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_4313_, 0, v_ty_4311_);
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
                        lean_dec(v___x_4306_);
                        v___x_4314_ = lean_box(0);
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
                v___x_4232_ = lean_box((v___x_4212_) as usize);
                v___f_4233_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__0___boxed
                        as *mut core::ffi::c_void,
                    15,
                    6,
                );
                lean_closure_set(v___f_4233_, 0, v___x_4218_);
                lean_closure_set(v___f_4233_, 1, v___x_4232_);
                lean_closure_set(v___f_4233_, 2, v_val_4231_);
                lean_closure_set(v___f_4233_, 3, v_eq_4230_);
                lean_closure_set(v___f_4233_, 4, v___y_4229_);
                lean_closure_set(v___f_4233_, 5, v___y_4226_);
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
                v___x_4247_ = lean_unsigned_to_nat(3);
                v___x_4248_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4247_);
                lean_dec(v_x_4201_);
                v___x_4249_ = l_Lean_Syntax_isNone(v___x_4248_);
                if v___x_4249_ == 0 {
                    lean_inc(v___x_4248_);
                    v___x_4250_ = l_Lean_Syntax_matchesNull(v___x_4248_, v___x_4235_);
                    if v___x_4250_ == 0 {
                        lean_dec(v___x_4248_);
                        lean_dec(v_ty_4238_);
                        lean_dec(v_c_4237_);
                        lean_dec(v___x_4218_);
                        v___x_4251_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_4251_;
                    } else {
                        v_eq_4252_ = l_Lean_Syntax_getArg(v___x_4248_, v___x_4216_);
                        v_val_4253_ = l_Lean_Syntax_getArg(v___x_4248_, v___x_4217_);
                        lean_dec(v___x_4248_);
                        v___x_4254_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4254_, 0, v_eq_4252_);
                        v___x_4255_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4255_, 0, v_val_4253_);
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
                    lean_dec(v___x_4248_);
                    v___x_4256_ = lean_box(0);
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
                v___f_4282_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___lam__1___boxed
                        as *mut core::ffi::c_void,
                    14,
                    5,
                );
                lean_closure_set(v___f_4282_, 0, v___x_4268_);
                lean_closure_set(v___f_4282_, 1, v_val_4281_);
                lean_closure_set(v___f_4282_, 2, v_eq_4280_);
                lean_closure_set(v___f_4282_, 3, v___y_4276_);
                lean_closure_set(v___f_4282_, 4, v___y_4279_);
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
                v___x_4296_ = lean_unsigned_to_nat(3);
                v___x_4297_ = l_Lean_Syntax_getArg(v_x_4201_, v___x_4296_);
                lean_dec(v_x_4201_);
                v___x_4298_ = l_Lean_Syntax_isNone(v___x_4297_);
                if v___x_4298_ == 0 {
                    lean_inc(v___x_4297_);
                    v___x_4299_ = l_Lean_Syntax_matchesNull(v___x_4297_, v___x_4284_);
                    if v___x_4299_ == 0 {
                        lean_dec(v___x_4297_);
                        lean_dec(v_ty_4287_);
                        lean_dec(v_c_4286_);
                        lean_dec(v___x_4268_);
                        v___x_4300_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg();
                        return v___x_4300_;
                    } else {
                        v_eq_4301_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_4266_);
                        v_val_4302_ = l_Lean_Syntax_getArg(v___x_4297_, v___x_4267_);
                        lean_dec(v___x_4297_);
                        v___x_4303_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4303_, 0, v_eq_4301_);
                        v___x_4304_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4304_, 0, v_val_4302_);
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
                    lean_dec(v___x_4297_);
                    v___x_4305_ = lean_box(0);
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
    mut v_x_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
    mut v_a_4317_: *mut LeanObject,
    mut v_a_4318_: *mut LeanObject,
    mut v_a_4319_: *mut LeanObject,
    mut v_a_4320_: *mut LeanObject,
    mut v_a_4321_: *mut LeanObject,
    mut v_a_4322_: *mut LeanObject,
    mut v_a_4323_: *mut LeanObject,
    mut v_a_4324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4325_: *mut LeanObject = core::ptr::null_mut();
    v_res_4325_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(
        v_x_4315_, v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_,
        v_a_4323_,
    );
    lean_dec(v_a_4323_);
    lean_dec_ref(v_a_4322_);
    lean_dec(v_a_4321_);
    lean_dec_ref(v_a_4320_);
    lean_dec(v_a_4319_);
    lean_dec_ref(v_a_4318_);
    lean_dec(v_a_4317_);
    lean_dec_ref(v_a_4316_);
    return v_res_4325_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1()
-> *mut LeanObject {
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    v___x_4334_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4335_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp___closed__1;
    v___x_4336_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1;
    v___x_4337_ = lean_alloc_closure(
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
    mut v_a_4339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4340_: *mut LeanObject = core::ptr::null_mut();
    v_res_4340_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
    return v_res_4340_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3()
-> *mut LeanObject {
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    v___x_4367_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1___closed__1;
    v___x_4368_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___closed__6;
    v___x_4369_ = l_Lean_addBuiltinDeclarationRanges(v___x_4367_, v___x_4368_);
    return v___x_4369_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3___boxed(
    mut v_a_4370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4371_: *mut LeanObject = core::ptr::null_mut();
    v_res_4371_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
    return v_res_4371_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(
    mut v_a_4372_: *mut LeanObject,
    mut v_a_4373_: *mut LeanObject,
    mut v_a_4374_: *mut LeanObject,
    mut v_a_4375_: *mut LeanObject,
    mut v_a_4376_: *mut LeanObject,
    mut v_a_4377_: *mut LeanObject,
    mut v_a_4378_: *mut LeanObject,
    mut v_a_4379_: *mut LeanObject,
    mut v_a_4380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    v___x_4382_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHyp(
        v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_,
        v_a_4380_,
    );
    return v___x_4382_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___boxed(
    mut v_a_4383_: *mut LeanObject,
    mut v_a_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
    mut v_a_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
    mut v_a_4388_: *mut LeanObject,
    mut v_a_4389_: *mut LeanObject,
    mut v_a_4390_: *mut LeanObject,
    mut v_a_4391_: *mut LeanObject,
    mut v_a_4392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4393_: *mut LeanObject = core::ptr::null_mut();
    v_res_4393_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv(
        v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_,
        v_a_4391_,
    );
    lean_dec(v_a_4391_);
    lean_dec_ref(v_a_4390_);
    lean_dec(v_a_4389_);
    lean_dec_ref(v_a_4388_);
    lean_dec(v_a_4387_);
    lean_dec_ref(v_a_4386_);
    lean_dec(v_a_4385_);
    lean_dec_ref(v_a_4384_);
    return v_res_4393_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1()
-> *mut LeanObject {
    let mut v___f_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    v___f_4402_ = lean_alloc_closure(
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
    mut v_a_4407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4408_: *mut LeanObject = core::ptr::null_mut();
    v_res_4408_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
    return v_res_4408_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3()
-> *mut LeanObject {
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    v___x_4435_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1___closed__1;
    v___x_4436_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___closed__6;
    v___x_4437_ = l_Lean_addBuiltinDeclarationRanges(v___x_4435_, v___x_4436_);
    return v___x_4437_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3___boxed(
    mut v_a_4438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4439_: *mut LeanObject = core::ptr::null_mut();
    v_res_4439_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
    return v_res_4439_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    v___x_4441_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
    v___x_4442_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4442_, 0, v___x_4441_);
    return v___x_4442_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg___boxed(
    mut v___y_4443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4444_: *mut LeanObject = core::ptr::null_mut();
    v_res_4444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
    return v_res_4444_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(
    mut v_00_u03b1_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    v___x_4449_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
    return v___x_4449_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___boxed(
    mut v_00_u03b1_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4454_: *mut LeanObject = core::ptr::null_mut();
    v_res_4454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0(v_00_u03b1_4450_, v___y_4451_, v___y_4452_);
    lean_dec(v___y_4452_);
    lean_dec_ref(v___y_4451_);
    return v_res_4454_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg()
-> *mut LeanObject {
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    v___x_4456_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__0___redArg___closed__0);
    v___x_4457_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4457_, 0, v___x_4456_);
    return v___x_4457_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg___boxed(
    mut v___y_4458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4459_: *mut LeanObject = core::ptr::null_mut();
    v_res_4459_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
    return v_res_4459_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(
    mut v_00_u03b1_4460_: *mut LeanObject,
    mut v___y_4461_: *mut LeanObject,
    mut v___y_4462_: *mut LeanObject,
    mut v___y_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
    return v___x_4468_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___boxed(
    mut v_00_u03b1_4469_: *mut LeanObject,
    mut v___y_4470_: *mut LeanObject,
    mut v___y_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4477_: *mut LeanObject = core::ptr::null_mut();
    v_res_4477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2(v_00_u03b1_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
    lean_dec(v___y_4475_);
    lean_dec_ref(v___y_4474_);
    lean_dec(v___y_4473_);
    lean_dec_ref(v___y_4472_);
    lean_dec(v___y_4471_);
    lean_dec_ref(v___y_4470_);
    return v_res_4477_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(
    mut v_opts_4478_: *mut LeanObject,
    mut v_opt_4479_: *mut LeanObject,
) -> u8 {
    let mut v_name_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    v_name_4480_ = lean_ctor_get(v_opt_4479_, 0);
    v_defValue_4481_ = lean_ctor_get(v_opt_4479_, 1);
    v_map_4482_ = lean_ctor_get(v_opts_4478_, 0);
    v___x_4483_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4482_,
            v_name_4480_,
        );
    if lean_obj_tag(v___x_4483_) == 0 {
        let mut v___x_4484_: u8 = 0;
        v___x_4484_ = (lean_unbox(v_defValue_4481_) as u8);
        return v___x_4484_;
    } else {
        let mut v_val_4485_: *mut LeanObject = core::ptr::null_mut();
        v_val_4485_ = lean_ctor_get(v___x_4483_, 0);
        lean_inc(v_val_4485_);
        lean_dec_ref_known(v___x_4483_, 1);
        if lean_obj_tag(v_val_4485_) == 1 {
            let mut v_v_4486_: u8 = 0;
            v_v_4486_ = lean_ctor_get_uint8(v_val_4485_, 0 as u32);
            lean_dec_ref_known(v_val_4485_, 0);
            return v_v_4486_;
        } else {
            let mut v___x_4487_: u8 = 0;
            lean_dec(v_val_4485_);
            v___x_4487_ = (lean_unbox(v_defValue_4481_) as u8);
            return v___x_4487_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3___boxed(
    mut v_opts_4488_: *mut LeanObject,
    mut v_opt_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4490_: u8 = 0;
    let mut v_r_4491_: *mut LeanObject = core::ptr::null_mut();
    v_res_4490_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_opts_4488_, v_opt_4489_);
    lean_dec_ref(v_opt_4489_);
    lean_dec_ref(v_opts_4488_);
    v_r_4491_ = lean_box((v_res_4490_) as usize);
    return v_r_4491_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    v___x_4492_ = lean_box(1);
    v___x_4493_ = l_Lean_MessageData_ofFormat(v___x_4492_);
    return v___x_4493_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    v___x_4497_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__2;
    v___x_4498_ = l_Lean_MessageData_ofFormat(v___x_4497_);
    return v___x_4498_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(
    mut v_x_4499_: *mut LeanObject,
    mut v_x_4500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4505_: u8 = 0;
    let mut v_before_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4509_: u8 = 0;
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_unused_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4524_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4500_) == 0 {
                    return v_x_4499_;
                } else {
                    v_head_4501_ = lean_ctor_get(v_x_4500_, 0);
                    v_tail_4502_ = lean_ctor_get(v_x_4500_, 1);
                    v_isSharedCheck_4524_ = (!lean_is_exclusive(v_x_4500_)) as u8;
                    if v_isSharedCheck_4524_ == 0 {
                        v___x_4504_ = v_x_4500_;
                        v_isShared_4505_ = v_isSharedCheck_4524_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4502_);
                        lean_inc(v_head_4501_);
                        lean_dec(v_x_4500_);
                        v___x_4504_ = lean_box(0);
                        v_isShared_4505_ = v_isSharedCheck_4524_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4506_ = lean_ctor_get(v_head_4501_, 0);
                v_isSharedCheck_4522_ = (!lean_is_exclusive(v_head_4501_)) as u8;
                if v_isSharedCheck_4522_ == 0 {
                    v_unused_4523_ = lean_ctor_get(v_head_4501_, 1);
                    lean_dec(v_unused_4523_);
                    v___x_4508_ = v_head_4501_;
                    v_isShared_4509_ = v_isSharedCheck_4522_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_4506_);
                    lean_dec(v_head_4501_);
                    v___x_4508_ = lean_box(0);
                    v_isShared_4509_ = v_isSharedCheck_4522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4510_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
                if v_isShared_4509_ == 0 {
                    lean_ctor_set_tag(v___x_4508_, 7);
                    lean_ctor_set(v___x_4508_, 1, v___x_4510_);
                    lean_ctor_set(v___x_4508_, 0, v_x_4499_);
                    v___x_4512_ = v___x_4508_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_x_4499_);
                    lean_ctor_set(v_reuseFailAlloc_4521_, 1, v___x_4510_);
                    v___x_4512_ = v_reuseFailAlloc_4521_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4513_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__3);
                if v_isShared_4505_ == 0 {
                    lean_ctor_set_tag(v___x_4504_, 7);
                    lean_ctor_set(v___x_4504_, 1, v___x_4513_);
                    lean_ctor_set(v___x_4504_, 0, v___x_4512_);
                    v___x_4515_ = v___x_4504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4520_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4512_);
                    lean_ctor_set(v_reuseFailAlloc_4520_, 1, v___x_4513_);
                    v___x_4515_ = v_reuseFailAlloc_4520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4516_ = l_Lean_MessageData_ofSyntax(v_before_4506_);
                v___x_4517_ = l_Lean_indentD(v___x_4516_);
                v___x_4518_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4518_, 0, v___x_4515_);
                lean_ctor_set(v___x_4518_, 1, v___x_4517_);
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
-> *mut LeanObject {
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    v___x_4528_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__1;
    v___x_4529_ = l_Lean_MessageData_ofFormat(v___x_4528_);
    return v___x_4529_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(
    mut v_msgData_4530_: *mut LeanObject,
    mut v_macroStack_4531_: *mut LeanObject,
    mut v___y_4532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: u8 = 0;
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut v_unused_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4534_ = lean_ctor_get(v___y_4532_, 2);
                v___x_4535_ = l_Lean_Elab_pp_macroStack;
                v___x_4536_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__3(v_options_4534_, v___x_4535_);
                if v___x_4536_ == 0 {
                    lean_dec(v_macroStack_4531_);
                    v___x_4537_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4537_, 0, v_msgData_4530_);
                    return v___x_4537_;
                } else {
                    if lean_obj_tag(v_macroStack_4531_) == 0 {
                        v___x_4538_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4538_, 0, v_msgData_4530_);
                        return v___x_4538_;
                    } else {
                        v_head_4539_ = lean_ctor_get(v_macroStack_4531_, 0);
                        lean_inc(v_head_4539_);
                        v_after_4540_ = lean_ctor_get(v_head_4539_, 1);
                        v_isSharedCheck_4555_ = (!lean_is_exclusive(v_head_4539_)) as u8;
                        if v_isSharedCheck_4555_ == 0 {
                            v_unused_4556_ = lean_ctor_get(v_head_4539_, 0);
                            lean_dec(v_unused_4556_);
                            v___x_4542_ = v_head_4539_;
                            v_isShared_4543_ = v_isSharedCheck_4555_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_4540_);
                            lean_dec(v_head_4539_);
                            v___x_4542_ = lean_box(0);
                            v_isShared_4543_ = v_isSharedCheck_4555_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4544_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4___closed__0);
                if v_isShared_4543_ == 0 {
                    lean_ctor_set_tag(v___x_4542_, 7);
                    lean_ctor_set(v___x_4542_, 1, v___x_4544_);
                    lean_ctor_set(v___x_4542_, 0, v_msgData_4530_);
                    v___x_4546_ = v___x_4542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_msgData_4530_);
                    lean_ctor_set(v_reuseFailAlloc_4554_, 1, v___x_4544_);
                    v___x_4546_ = v_reuseFailAlloc_4554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4547_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___closed__2);
                v___x_4548_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4548_, 0, v___x_4546_);
                lean_ctor_set(v___x_4548_, 1, v___x_4547_);
                v___x_4549_ = l_Lean_MessageData_ofSyntax(v_after_4540_);
                v___x_4550_ = l_Lean_indentD(v___x_4549_);
                v_msgData_4551_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_4551_, 0, v___x_4548_);
                lean_ctor_set(v_msgData_4551_, 1, v___x_4550_);
                v___x_4552_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1_spec__4(v_msgData_4551_, v_macroStack_4531_);
                v___x_4553_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4553_, 0, v___x_4552_);
                return v___x_4553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg___boxed(
    mut v_msgData_4557_: *mut LeanObject,
    mut v_macroStack_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4561_: *mut LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_4557_, v_macroStack_4558_, v___y_4559_);
    lean_dec_ref(v___y_4559_);
    return v_res_4561_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(
    mut v_msg_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
    mut v___y_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4570_ = lean_ctor_get(v___y_4567_, 5);
                v___x_4571_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExpr_spec__1_spec__1(v_msg_4562_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
                v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
                lean_inc(v_a_4572_);
                lean_dec_ref(v___x_4571_);
                v_macroStack_4573_ = lean_ctor_get(v___y_4563_, 1);
                v___x_4574_ = l_Lean_Elab_getBetterRef(v_ref_4570_, v_macroStack_4573_);
                lean_inc(v_macroStack_4573_);
                v___x_4575_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_a_4572_, v_macroStack_4573_, v___y_4567_);
                v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
                v_isSharedCheck_4584_ = (!lean_is_exclusive(v___x_4575_)) as u8;
                if v_isSharedCheck_4584_ == 0 {
                    v___x_4578_ = v___x_4575_;
                    v_isShared_4579_ = v_isSharedCheck_4584_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4576_);
                    lean_dec(v___x_4575_);
                    v___x_4578_ = lean_box(0);
                    v_isShared_4579_ = v_isSharedCheck_4584_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4580_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4580_, 0, v___x_4574_);
                lean_ctor_set(v___x_4580_, 1, v_a_4576_);
                if v_isShared_4579_ == 0 {
                    lean_ctor_set_tag(v___x_4578_, 1);
                    lean_ctor_set(v___x_4578_, 0, v___x_4580_);
                    v___x_4582_ = v___x_4578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4580_);
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
    mut v_msg_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
    mut v___y_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
    mut v___y_4592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4593_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4591_);
    lean_dec_ref(v___y_4590_);
    lean_dec(v___y_4589_);
    lean_dec_ref(v___y_4588_);
    lean_dec(v___y_4587_);
    lean_dec_ref(v___y_4586_);
    return v_res_4593_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0(
    mut v_eq_4594_: *mut LeanObject,
    mut v_r_4595_: *mut LeanObject,
    mut v_p_4596_: *mut LeanObject,
    mut v_x_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
    mut v___y_4600_: *mut LeanObject,
    mut v___y_4601_: *mut LeanObject,
    mut v___y_4602_: *mut LeanObject,
    mut v___y_4603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4611_: u8 = 0;
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v_a_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4636_: u8 = 0;
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4640_: u8 = 0;
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4605_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind(v_eq_4594_);
                if lean_obj_tag(v___x_4605_) == 1 {
                    v_val_4606_ = lean_ctor_get(v___x_4605_, 0);
                    lean_inc_n(v_val_4606_, 2);
                    lean_dec_ref_known(v___x_4605_, 1);
                    lean_inc(v_p_4596_);
                    lean_inc(v_r_4595_);
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
                    if lean_obj_tag(v___x_4607_) == 0 {
                        v_a_4608_ = lean_ctor_get(v___x_4607_, 0);
                        v_isSharedCheck_4632_ = (!lean_is_exclusive(v___x_4607_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4610_ = v___x_4607_;
                            v_isShared_4611_ = v_isSharedCheck_4632_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4608_);
                            lean_dec(v___x_4607_);
                            v___x_4610_ = lean_box(0);
                            v_isShared_4611_ = v_isSharedCheck_4632_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_4606_);
                        lean_dec(v_p_4596_);
                        lean_dec(v_r_4595_);
                        v_a_4633_ = lean_ctor_get(v___x_4607_, 0);
                        v_isSharedCheck_4640_ = (!lean_is_exclusive(v___x_4607_)) as u8;
                        if v_isSharedCheck_4640_ == 0 {
                            v___x_4635_ = v___x_4607_;
                            v_isShared_4636_ = v_isSharedCheck_4640_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4633_);
                            lean_dec(v___x_4607_);
                            v___x_4635_ = lean_box(0);
                            v_isShared_4636_ = v_isSharedCheck_4640_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4605_);
                    lean_dec(v_p_4596_);
                    lean_dec(v_r_4595_);
                    v___x_4641_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__2___redArg();
                    return v___x_4641_;
                }
            }
            1 => {
                v___x_4612_ = (lean_unbox(v_a_4608_) as u8);
                lean_dec(v_a_4608_);
                if v___x_4612_ == 0 {
                    lean_del_object(v___x_4610_);
                    v___x_4613_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__1,
                    );
                    v___x_4614_ = l_Lean_MessageData_ofSyntax(v_r_4595_);
                    v___x_4615_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4615_, 0, v___x_4613_);
                    lean_ctor_set(v___x_4615_, 1, v___x_4614_);
                    v___x_4616_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__3,
                    );
                    v___x_4617_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4617_, 0, v___x_4615_);
                    lean_ctor_set(v___x_4617_, 1, v___x_4616_);
                    v___x_4618_ = l_Lean_Elab_Tactic_GuardExpr_MatchKind_toStringDescr(v_val_4606_);
                    lean_dec(v_val_4606_);
                    v___x_4619_ = l_Lean_stringToMessageData(v___x_4618_);
                    v___x_4620_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4620_, 0, v___x_4617_);
                    lean_ctor_set(v___x_4620_, 1, v___x_4619_);
                    v___x_4621_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__5,
                    );
                    v___x_4622_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4622_, 0, v___x_4620_);
                    lean_ctor_set(v___x_4622_, 1, v___x_4621_);
                    v___x_4623_ = l_Lean_MessageData_ofSyntax(v_p_4596_);
                    v___x_4624_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4624_, 0, v___x_4622_);
                    lean_ctor_set(v___x_4624_, 1, v___x_4623_);
                    v___x_4625_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardExpr___lam__0___closed__7,
                    );
                    v___x_4626_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4626_, 0, v___x_4624_);
                    lean_ctor_set(v___x_4626_, 1, v___x_4625_);
                    v___x_4627_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_4626_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
                    return v___x_4627_;
                } else {
                    lean_dec(v_val_4606_);
                    lean_dec(v_p_4596_);
                    lean_dec(v_r_4595_);
                    v___x_4628_ = lean_box(0);
                    if v_isShared_4611_ == 0 {
                        lean_ctor_set(v___x_4610_, 0, v___x_4628_);
                        v___x_4630_ = v___x_4610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4631_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
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
                    v_reuseFailAlloc_4639_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_a_4633_);
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
    mut v_eq_4642_: *mut LeanObject,
    mut v_r_4643_: *mut LeanObject,
    mut v_p_4644_: *mut LeanObject,
    mut v_x_4645_: *mut LeanObject,
    mut v___y_4646_: *mut LeanObject,
    mut v___y_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4653_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4651_);
    lean_dec_ref(v___y_4650_);
    lean_dec(v___y_4649_);
    lean_dec_ref(v___y_4648_);
    lean_dec(v___y_4647_);
    lean_dec_ref(v___y_4646_);
    lean_dec_ref(v_x_4645_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(
    mut v_x_4661_: *mut LeanObject,
    mut v_a_4662_: *mut LeanObject,
    mut v_a_4663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: u8 = 0;
    v___x_4665_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
    lean_inc(v_x_4661_);
    v___x_4666_ = l_Lean_Syntax_isOfKind(v_x_4661_, v___x_4665_);
    if v___x_4666_ == 0 {
        let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4661_);
        v___x_4667_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
        return v___x_4667_;
    } else {
        let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
        let mut v_eq_4669_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4671_: u8 = 0;
        v___x_4668_ = lean_unsigned_to_nat(2);
        v_eq_4669_ = l_Lean_Syntax_getArg(v_x_4661_, v___x_4668_);
        v___x_4670_ = l_Lean_Elab_Tactic_GuardExpr_equal_toMatchKind___closed__1;
        lean_inc(v_eq_4669_);
        v___x_4671_ = l_Lean_Syntax_isOfKind(v_eq_4669_, v___x_4670_);
        if v___x_4671_ == 0 {
            let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_eq_4669_);
            lean_dec(v_x_4661_);
            v___x_4672_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
            return v___x_4672_;
        } else {
            let mut v___x_4673_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_4674_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_4676_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_4677_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
            v___x_4673_ = lean_unsigned_to_nat(1);
            v_r_4674_ = l_Lean_Syntax_getArg(v_x_4661_, v___x_4673_);
            v___x_4675_ = lean_unsigned_to_nat(3);
            v_p_4676_ = l_Lean_Syntax_getArg(v_x_4661_, v___x_4675_);
            lean_dec(v_x_4661_);
            v___f_4677_ = lean_alloc_closure(
                l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___lam__0___boxed
                    as *mut core::ffi::c_void,
                11,
                3,
            );
            lean_closure_set(v___f_4677_, 0, v_eq_4669_);
            lean_closure_set(v___f_4677_, 1, v_r_4674_);
            lean_closure_set(v___f_4677_, 2, v_p_4676_);
            v___x_4678_ =
                l_Lean_Elab_Command_runTermElabM___redArg(v___f_4677_, v_a_4662_, v_a_4663_);
            return v___x_4678_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___boxed(
    mut v_x_4679_: *mut LeanObject,
    mut v_a_4680_: *mut LeanObject,
    mut v_a_4681_: *mut LeanObject,
    mut v_a_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4683_: *mut LeanObject = core::ptr::null_mut();
    v_res_4683_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd(v_x_4679_, v_a_4680_, v_a_4681_);
    lean_dec(v_a_4681_);
    lean_dec_ref(v_a_4680_);
    return v_res_4683_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1(
    mut v_00_u03b1_4684_: *mut LeanObject,
    mut v_msg_4685_: *mut LeanObject,
    mut v___y_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4694_: *mut LeanObject,
    mut v_msg_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
    mut v___y_4698_: *mut LeanObject,
    mut v___y_4699_: *mut LeanObject,
    mut v___y_4700_: *mut LeanObject,
    mut v___y_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4703_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4701_);
    lean_dec_ref(v___y_4700_);
    lean_dec(v___y_4699_);
    lean_dec_ref(v___y_4698_);
    lean_dec(v___y_4697_);
    lean_dec_ref(v___y_4696_);
    return v_res_4703_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(
    mut v_msgData_4704_: *mut LeanObject,
    mut v_macroStack_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
    mut v___y_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    v___x_4713_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___redArg(v_msgData_4704_, v_macroStack_4705_, v___y_4710_);
    return v___x_4713_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1___boxed(
    mut v_msgData_4714_: *mut LeanObject,
    mut v_macroStack_4715_: *mut LeanObject,
    mut v___y_4716_: *mut LeanObject,
    mut v___y_4717_: *mut LeanObject,
    mut v___y_4718_: *mut LeanObject,
    mut v___y_4719_: *mut LeanObject,
    mut v___y_4720_: *mut LeanObject,
    mut v___y_4721_: *mut LeanObject,
    mut v___y_4722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4723_: *mut LeanObject = core::ptr::null_mut();
    v_res_4723_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1_spec__1(v_msgData_4714_, v_macroStack_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
    lean_dec(v___y_4721_);
    lean_dec_ref(v___y_4720_);
    lean_dec(v___y_4719_);
    lean_dec_ref(v___y_4718_);
    lean_dec(v___y_4717_);
    lean_dec_ref(v___y_4716_);
    return v_res_4723_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1()
-> *mut LeanObject {
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    v___x_4732_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4733_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___closed__2;
    v___x_4734_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1;
    v___x_4735_ = lean_alloc_closure(
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
    mut v_a_4737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4738_: *mut LeanObject = core::ptr::null_mut();
    v_res_4738_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
    return v_res_4738_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3()
-> *mut LeanObject {
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    v___x_4765_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1___closed__1;
    v___x_4766_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___closed__6;
    v___x_4767_ = l_Lean_addBuiltinDeclarationRanges(v___x_4765_, v___x_4766_);
    return v___x_4767_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3___boxed(
    mut v_a_4768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4769_: *mut LeanObject = core::ptr::null_mut();
    v_res_4769_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
    return v_res_4769_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2()
-> *mut LeanObject {
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut LeanObject = core::ptr::null_mut();
    v___x_4773_ = lean_box(0);
    v___x_4774_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__1;
    v___x_4775_ = l_Lean_mkConst(v___x_4774_, v___x_4773_);
    return v___x_4775_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(
    mut v_e_4776_: *mut LeanObject,
    mut v_a_4777_: *mut LeanObject,
    mut v_a_4778_: *mut LeanObject,
    mut v_a_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: u8 = 0;
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    v___x_4782_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once), _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
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
    mut v_e_4786_: *mut LeanObject,
    mut v_a_4787_: *mut LeanObject,
    mut v_a_4788_: *mut LeanObject,
    mut v_a_4789_: *mut LeanObject,
    mut v_a_4790_: *mut LeanObject,
    mut v_a_4791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4792_: *mut LeanObject = core::ptr::null_mut();
    v_res_4792_ =
        l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(
            v_e_4786_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_,
        );
    lean_dec(v_a_4790_);
    lean_dec_ref(v_a_4789_);
    lean_dec(v_a_4788_);
    lean_dec_ref(v_a_4787_);
    return v_res_4792_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    v___x_4794_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__0;
    v___x_4795_ = l_Lean_stringToMessageData(v___x_4794_);
    return v___x_4795_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    v___x_4797_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__2;
    v___x_4798_ = l_Lean_stringToMessageData(v___x_4797_);
    return v___x_4798_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0(
    mut v___x_4799_: *mut LeanObject,
    mut v___x_4800_: *mut LeanObject,
    mut v___x_4801_: u8,
    mut v___x_4802_: *mut LeanObject,
    mut v___y_4803_: *mut LeanObject,
    mut v___y_4804_: *mut LeanObject,
    mut v___y_4805_: *mut LeanObject,
    mut v___y_4806_: *mut LeanObject,
    mut v___y_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u8 = 0;
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4825_: u8 = 0;
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4830_: u8 = 0;
    let mut v_unused_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4835_: u8 = 0;
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4839_: u8 = 0;
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4844_: u8 = 0;
    let mut v___x_4845_: u8 = 0;
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v_a_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4860_: u8 = 0;
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4864_: u8 = 0;
    let mut v_a_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4868_: u8 = 0;
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut v_a_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4876_: u8 = 0;
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4810_) == 0 {
                    v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
                    lean_inc(v_a_4811_);
                    lean_dec_ref_known(v___x_4810_, 1);
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
                    if lean_obj_tag(v___x_4813_) == 0 {
                        lean_dec_ref_known(v___x_4813_, 1);
                        v___x_4814_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_GuardExpr_elabAndEvalMatchKind_spec__0___redArg(v_a_4811_, v___y_4806_);
                        v_a_4815_ = lean_ctor_get(v___x_4814_, 0);
                        lean_inc_n(v_a_4815_, 2);
                        lean_dec_ref(v___x_4814_);
                        v___x_4816_ = l_Lean_Meta_getMVars(
                            v_a_4815_,
                            v___y_4805_,
                            v___y_4806_,
                            v___y_4807_,
                            v___y_4808_,
                        );
                        if lean_obj_tag(v___x_4816_) == 0 {
                            v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
                            lean_inc(v_a_4817_);
                            lean_dec_ref_known(v___x_4816_, 1);
                            v___x_4818_ = lean_array_get_size(v_a_4817_);
                            v___x_4819_ = lean_unsigned_to_nat(0);
                            v___x_4820_ = lean_nat_dec_eq(v___x_4818_, v___x_4819_);
                            if v___x_4820_ == 0 {
                                lean_dec(v_a_4815_);
                                v___x_4821_ = lean_box(0);
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
                                lean_dec(v_a_4817_);
                                if lean_obj_tag(v___x_4822_) == 0 {
                                    v_isSharedCheck_4830_ = (!lean_is_exclusive(v___x_4822_)) as u8;
                                    if v_isSharedCheck_4830_ == 0 {
                                        v_unused_4831_ = lean_ctor_get(v___x_4822_, 0);
                                        lean_dec(v_unused_4831_);
                                        v___x_4824_ = v___x_4822_;
                                        v_isShared_4825_ = v_isSharedCheck_4830_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v___x_4822_);
                                        v___x_4824_ = lean_box(0);
                                        v_isShared_4825_ = v_isSharedCheck_4830_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v_a_4832_ = lean_ctor_get(v___x_4822_, 0);
                                    v_isSharedCheck_4839_ = (!lean_is_exclusive(v___x_4822_)) as u8;
                                    if v_isSharedCheck_4839_ == 0 {
                                        v___x_4834_ = v___x_4822_;
                                        v_isShared_4835_ = v_isSharedCheck_4839_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4832_);
                                        lean_dec(v___x_4822_);
                                        v___x_4834_ = lean_box(0);
                                        v_isShared_4835_ = v_isSharedCheck_4839_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_4817_);
                                lean_inc(v_a_4815_);
                                v___x_4840_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1(v_a_4815_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
                                if lean_obj_tag(v___x_4840_) == 0 {
                                    v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
                                    v_isSharedCheck_4856_ = (!lean_is_exclusive(v___x_4840_)) as u8;
                                    if v_isSharedCheck_4856_ == 0 {
                                        v___x_4843_ = v___x_4840_;
                                        v_isShared_4844_ = v_isSharedCheck_4856_;
                                        state = 5;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4841_);
                                        lean_dec(v___x_4840_);
                                        v___x_4843_ = lean_box(0);
                                        v_isShared_4844_ = v_isSharedCheck_4856_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4815_);
                                    v_a_4857_ = lean_ctor_get(v___x_4840_, 0);
                                    v_isSharedCheck_4864_ = (!lean_is_exclusive(v___x_4840_)) as u8;
                                    if v_isSharedCheck_4864_ == 0 {
                                        v___x_4859_ = v___x_4840_;
                                        v_isShared_4860_ = v_isSharedCheck_4864_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4857_);
                                        lean_dec(v___x_4840_);
                                        v___x_4859_ = lean_box(0);
                                        v_isShared_4860_ = v_isSharedCheck_4864_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_4815_);
                            v_a_4865_ = lean_ctor_get(v___x_4816_, 0);
                            v_isSharedCheck_4872_ = (!lean_is_exclusive(v___x_4816_)) as u8;
                            if v_isSharedCheck_4872_ == 0 {
                                v___x_4867_ = v___x_4816_;
                                v_isShared_4868_ = v_isSharedCheck_4872_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_4865_);
                                lean_dec(v___x_4816_);
                                v___x_4867_ = lean_box(0);
                                v_isShared_4868_ = v_isSharedCheck_4872_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4811_);
                        return v___x_4813_;
                    }
                } else {
                    v_a_4873_ = lean_ctor_get(v___x_4810_, 0);
                    v_isSharedCheck_4880_ = (!lean_is_exclusive(v___x_4810_)) as u8;
                    if v_isSharedCheck_4880_ == 0 {
                        v___x_4875_ = v___x_4810_;
                        v_isShared_4876_ = v_isSharedCheck_4880_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4873_);
                        lean_dec(v___x_4810_);
                        v___x_4875_ = lean_box(0);
                        v_isShared_4876_ = v_isSharedCheck_4880_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4826_ = lean_box(0);
                if v_isShared_4825_ == 0 {
                    lean_ctor_set(v___x_4824_, 0, v___x_4826_);
                    v___x_4828_ = v___x_4824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4826_);
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
                    v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
                    v___x_4837_ = v_reuseFailAlloc_4838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4837_;
            }
            5 => {
                v___x_4845_ = (lean_unbox(v_a_4841_) as u8);
                lean_dec(v_a_4841_);
                if v___x_4845_ == 0 {
                    lean_del_object(v___x_4843_);
                    v___x_4846_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__1,
                    );
                    v___x_4847_ = l_Lean_indentExpr(v_a_4815_);
                    v___x_4848_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4848_, 0, v___x_4846_);
                    lean_ctor_set(v___x_4848_, 1, v___x_4847_);
                    v___x_4849_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___closed__3,
                    );
                    v___x_4850_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4850_, 0, v___x_4848_);
                    lean_ctor_set(v___x_4850_, 1, v___x_4849_);
                    v___x_4851_ = l_Lean_throwError___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__1___redArg(v___x_4850_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
                    return v___x_4851_;
                } else {
                    lean_dec(v_a_4815_);
                    v___x_4852_ = lean_box(0);
                    if v_isShared_4844_ == 0 {
                        lean_ctor_set(v___x_4843_, 0, v___x_4852_);
                        v___x_4854_ = v___x_4843_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4855_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4852_);
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
                    v_reuseFailAlloc_4863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_a_4857_);
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
                    v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4871_, 0, v_a_4865_);
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
                    v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
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
    mut v___x_4881_: *mut LeanObject,
    mut v___x_4882_: *mut LeanObject,
    mut v___x_4883_: *mut LeanObject,
    mut v___x_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1792__boxed_4892_: u8 = 0;
    let mut v_res_4893_: *mut LeanObject = core::ptr::null_mut();
    v___x_1792__boxed_4892_ = (lean_unbox(v___x_4883_) as u8);
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
    lean_dec(v___y_4890_);
    lean_dec_ref(v___y_4889_);
    lean_dec(v___y_4888_);
    lean_dec_ref(v___y_4887_);
    lean_dec(v___y_4886_);
    lean_dec_ref(v___y_4885_);
    return v_res_4893_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2() -> *mut LeanObject {
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    v___x_4900_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2_once), _init_l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd_unsafe__1___closed__2);
    v___x_4901_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4901_, 0, v___x_4900_);
    return v___x_4901_;
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(
    mut v_x_4902_: *mut LeanObject,
    mut v_a_4903_: *mut LeanObject,
    mut v_a_4904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: u8 = 0;
    v___x_4906_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
    lean_inc(v_x_4902_);
    v___x_4907_ = l_Lean_Syntax_isOfKind(v_x_4902_, v___x_4906_);
    if v___x_4907_ == 0 {
        let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_4902_);
        v___x_4908_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_spec__0___redArg();
        return v___x_4908_;
    } else {
        let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_4914_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
        v___x_4909_ = lean_unsigned_to_nat(1);
        v___x_4910_ = l_Lean_Syntax_getArg(v_x_4902_, v___x_4909_);
        lean_dec(v_x_4902_);
        v___x_4911_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2_once),
            _init_l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__2,
        );
        v___x_4912_ = lean_box(0);
        v___x_4913_ = lean_box((v___x_4907_) as usize);
        v___f_4914_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___lam__0___boxed as *mut core::ffi::c_void,
            11,
            4,
        );
        lean_closure_set(v___f_4914_, 0, v___x_4910_);
        lean_closure_set(v___f_4914_, 1, v___x_4911_);
        lean_closure_set(v___f_4914_, 2, v___x_4913_);
        lean_closure_set(v___f_4914_, 3, v___x_4912_);
        v___x_4915_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_4914_, v_a_4903_, v_a_4904_);
        return v___x_4915_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___boxed(
    mut v_x_4916_: *mut LeanObject,
    mut v_a_4917_: *mut LeanObject,
    mut v_a_4918_: *mut LeanObject,
    mut v_a_4919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4920_: *mut LeanObject = core::ptr::null_mut();
    v_res_4920_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd(v_x_4916_, v_a_4917_, v_a_4918_);
    lean_dec(v_a_4918_);
    lean_dec_ref(v_a_4917_);
    return v_res_4920_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1()
-> *mut LeanObject {
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    v___x_4929_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4930_ = l_Lean_Elab_Tactic_GuardExpr_evalGuardCmd___closed__1;
    v___x_4931_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1;
    v___x_4932_ = lean_alloc_closure(
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
    mut v_a_4934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4935_: *mut LeanObject = core::ptr::null_mut();
    v_res_4935_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
    return v_res_4935_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3()
-> *mut LeanObject {
    let mut v___x_4962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut LeanObject = core::ptr::null_mut();
    v___x_4962_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1___closed__1;
    v___x_4963_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___closed__6;
    v___x_4964_ = l_Lean_addBuiltinDeclarationRanges(v___x_4962_, v___x_4963_);
    return v___x_4964_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3___boxed(
    mut v_a_4965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4966_: *mut LeanObject = core::ptr::null_mut();
    v_res_4966_ = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
    return v_res_4966_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Guard(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Guard(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExpr___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExpr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprConv_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTarget___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTarget_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardTargetConv_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHyp___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHyp_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardHypConv___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardHypConv_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardExprCmd_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Guard_0__Lean_Elab_Tactic_GuardExpr_evalGuardCmd___regBuiltin_Lean_Elab_Tactic_GuardExpr_evalGuardCmd_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Guard(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Guard(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Guard(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Guard(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Guard(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Guard(builtin);
}
