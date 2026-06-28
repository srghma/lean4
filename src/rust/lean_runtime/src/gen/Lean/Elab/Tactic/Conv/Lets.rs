// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Lets
// Imports: Lean.Elab.Tactic.Lets Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getNameOfIdent_x27,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_changeLhs,
    l_Lean_Elab_Tactic_Conv_getLhs___redArg, l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg,
    l_Lean_Elab_Tactic_Conv_mkConvGoalFor, runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Lets::{
    initialize_Lean_Elab_Tactic_Lets, l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg,
    l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg, l_Lean_Elab_Tactic_extractLetsAddVarInfo,
    runtime_initialize_Lean_Elab_Tactic_Lets,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvar___override, l_Lean_Expr_mvar___override, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_isExprDefEq,
    l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::LetToHave::l_Lean_Meta_letToHave;
use crate::r#gen::Lean::Meta::Tactic::Lets::{
    l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp, l_Lean_Meta_liftLets,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_8, lean_box,
    lean_box_usize, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value: LeanStringObject<
    41,
> = LeanStringObject {
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
        40, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 41, 32, 110, 111,
        110, 45, 100, 101, 102, 101, 113, 32, 105, 110, 32, 97, 115, 115, 105, 103, 110, 109, 101,
        110, 116, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value: LeanStringObject<
    17,
> = LeanStringObject {
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
        109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value: LeanStringObject<
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
    m_data: [101, 120, 116, 114, 97, 99, 116, 95, 108, 101, 116, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__0_value)
                as *mut LeanObject,
            4644032510077903208 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value: LeanStringObject<5> =
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
        m_data: [67, 111, 110, 118, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value: LeanStringObject<12> =
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
        m_data: [101, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__4_value)
                as *mut LeanObject,
            3123354491248406356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value: LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__6_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut LeanObject)],
    };
pub static mut l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [101, 118, 97, 108, 69, 120, 116, 114, 97, 99, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__1_value) as *mut LeanObject,4698081872094885029 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value: LeanStringObject<10> =
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
        m_data: [108, 105, 102, 116, 95, 108, 101, 116, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__0_value)
                as *mut LeanObject,
            7326091052943921366 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value: LeanStringObject<9> =
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
        m_data: [108, 105, 102, 116, 76, 101, 116, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__0_value)
                as *mut LeanObject,
            15211363250062378073 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 76, 105, 102, 116, 76, 101, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__0_value) as *mut LeanObject,5567011710448919931 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value: LeanStringObject<12> =
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
        m_data: [108, 101, 116, 95, 116, 111, 95, 104, 97, 118, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__0_value)
                as *mut LeanObject,
            6130153969274943757 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value: LeanStringObject<10> =
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
        m_data: [108, 101, 116, 84, 111, 72, 97, 118, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value)
                as *mut LeanObject,
            2622230176999461939 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value_aux_3)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__0_value)
                as *mut LeanObject,
            1576434579341158445 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 118, 97, 108, 76, 101, 116, 84, 111, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__3_value) as *mut LeanObject,9299793053028177184 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__0_value) as *mut LeanObject,7421465252802819374 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    v___x_1102_ = lean_box(0);
    v___x_1103_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1104_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    lean_ctor_set(v___x_1104_, 1, v___x_1102_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v___x_1106_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___closed__0);
    v___x_1107_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg___boxed(
    mut v___y_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
    return v_res_1109_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(
    mut v_00_u03b1_1110_: *mut LeanObject,
    mut v___y_1111_: *mut LeanObject,
    mut v___y_1112_: *mut LeanObject,
    mut v___y_1113_: *mut LeanObject,
    mut v___y_1114_: *mut LeanObject,
    mut v___y_1115_: *mut LeanObject,
    mut v___y_1116_: *mut LeanObject,
    mut v___y_1117_: *mut LeanObject,
    mut v___y_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
    return v___x_1120_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___boxed(
    mut v_00_u03b1_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
    mut v___y_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1131_: *mut LeanObject = core::ptr::null_mut();
    v_res_1131_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0(
            v_00_u03b1_1121_,
            v___y_1122_,
            v___y_1123_,
            v___y_1124_,
            v___y_1125_,
            v___y_1126_,
            v___y_1127_,
            v___y_1128_,
            v___y_1129_,
        );
    lean_dec(v___y_1129_);
    lean_dec_ref(v___y_1128_);
    lean_dec(v___y_1127_);
    lean_dec_ref(v___y_1126_);
    lean_dec(v___y_1125_);
    lean_dec_ref(v___y_1124_);
    lean_dec(v___y_1123_);
    lean_dec_ref(v___y_1122_);
    return v_res_1131_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
    mut v_mvarId_1132_: *mut LeanObject,
    mut v_x_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1139_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1132_,
                    v_x_1133_,
                    v___y_1134_,
                    v___y_1135_,
                    v___y_1136_,
                    v___y_1137_,
                );
                if lean_obj_tag(v___x_1139_) == 0 {
                    v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
                    v_isSharedCheck_1147_ = (!lean_is_exclusive(v___x_1139_)) as u8;
                    if v_isSharedCheck_1147_ == 0 {
                        v___x_1142_ = v___x_1139_;
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1140_);
                        lean_dec(v___x_1139_);
                        v___x_1142_ = lean_box(0);
                        v_isShared_1143_ = v_isSharedCheck_1147_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1148_ = lean_ctor_get(v___x_1139_, 0);
                    v_isSharedCheck_1155_ = (!lean_is_exclusive(v___x_1139_)) as u8;
                    if v_isSharedCheck_1155_ == 0 {
                        v___x_1150_ = v___x_1139_;
                        v_isShared_1151_ = v_isSharedCheck_1155_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1148_);
                        lean_dec(v___x_1139_);
                        v___x_1150_ = lean_box(0);
                        v_isShared_1151_ = v_isSharedCheck_1155_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1143_ == 0 {
                    v___x_1145_ = v___x_1142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1145_;
            }
            3 => {
                if v_isShared_1151_ == 0 {
                    v___x_1153_ = v___x_1150_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
                    v___x_1153_ = v_reuseFailAlloc_1154_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg___boxed(
    mut v_mvarId_1156_: *mut LeanObject,
    mut v_x_1157_: *mut LeanObject,
    mut v___y_1158_: *mut LeanObject,
    mut v___y_1159_: *mut LeanObject,
    mut v___y_1160_: *mut LeanObject,
    mut v___y_1161_: *mut LeanObject,
    mut v___y_1162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1163_: *mut LeanObject = core::ptr::null_mut();
    v_res_1163_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
            v_mvarId_1156_,
            v_x_1157_,
            v___y_1158_,
            v___y_1159_,
            v___y_1160_,
            v___y_1161_,
        );
    lean_dec(v___y_1161_);
    lean_dec_ref(v___y_1160_);
    lean_dec(v___y_1159_);
    lean_dec_ref(v___y_1158_);
    return v_res_1163_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(
    mut v_00_u03b1_1164_: *mut LeanObject,
    mut v_mvarId_1165_: *mut LeanObject,
    mut v_x_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(
            v_mvarId_1165_,
            v_x_1166_,
            v___y_1167_,
            v___y_1168_,
            v___y_1169_,
            v___y_1170_,
        );
    return v___x_1172_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___boxed(
    mut v_00_u03b1_1173_: *mut LeanObject,
    mut v_mvarId_1174_: *mut LeanObject,
    mut v_x_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
    mut v___y_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1181_: *mut LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4(
        v_00_u03b1_1173_,
        v_mvarId_1174_,
        v_x_1175_,
        v___y_1176_,
        v___y_1177_,
        v___y_1178_,
        v___y_1179_,
    );
    lean_dec(v___y_1179_);
    lean_dec_ref(v___y_1178_);
    lean_dec(v___y_1177_);
    lean_dec_ref(v___y_1176_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(
    mut v_k_1182_: *mut LeanObject,
    mut v_b_1183_: *mut LeanObject,
    mut v_c_1184_: *mut LeanObject,
    mut v_d_1185_: *mut LeanObject,
    mut v___y_1186_: *mut LeanObject,
    mut v___y_1187_: *mut LeanObject,
    mut v___y_1188_: *mut LeanObject,
    mut v___y_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1189_);
    lean_inc_ref(v___y_1188_);
    lean_inc(v___y_1187_);
    lean_inc_ref(v___y_1186_);
    v___x_1191_ = lean_apply_8(
        v_k_1182_,
        v_b_1183_,
        v_c_1184_,
        v_d_1185_,
        v___y_1186_,
        v___y_1187_,
        v___y_1188_,
        v___y_1189_,
        lean_box(0),
    );
    return v___x_1191_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed(
    mut v_k_1192_: *mut LeanObject,
    mut v_b_1193_: *mut LeanObject,
    mut v_c_1194_: *mut LeanObject,
    mut v_d_1195_: *mut LeanObject,
    mut v___y_1196_: *mut LeanObject,
    mut v___y_1197_: *mut LeanObject,
    mut v___y_1198_: *mut LeanObject,
    mut v___y_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1201_: *mut LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0(v_k_1192_, v_b_1193_, v_c_1194_, v_d_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
    lean_dec(v___y_1199_);
    lean_dec_ref(v___y_1198_);
    lean_dec(v___y_1197_);
    lean_dec_ref(v___y_1196_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(
    mut v_es_1202_: *mut LeanObject,
    mut v_givenNames_1203_: *mut LeanObject,
    mut v_k_1204_: *mut LeanObject,
    mut v_config_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
    mut v___y_1208_: *mut LeanObject,
    mut v___y_1209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1216_: u8 = 0;
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut v_a_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1211_ = lean_alloc_closure(l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                lean_closure_set(v___f_1211_, 0, v_k_1204_);
                v___x_1212_ = l___private_Lean_Meta_Tactic_Lets_0__Lean_Meta_extractLetsImp(
                    lean_box(0),
                    v_es_1202_,
                    v_givenNames_1203_,
                    v___f_1211_,
                    v_config_1205_,
                    v___y_1206_,
                    v___y_1207_,
                    v___y_1208_,
                    v___y_1209_,
                );
                if lean_obj_tag(v___x_1212_) == 0 {
                    v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
                    v_isSharedCheck_1220_ = (!lean_is_exclusive(v___x_1212_)) as u8;
                    if v_isSharedCheck_1220_ == 0 {
                        v___x_1215_ = v___x_1212_;
                        v_isShared_1216_ = v_isSharedCheck_1220_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1213_);
                        lean_dec(v___x_1212_);
                        v___x_1215_ = lean_box(0);
                        v_isShared_1216_ = v_isSharedCheck_1220_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1221_ = lean_ctor_get(v___x_1212_, 0);
                    v_isSharedCheck_1228_ = (!lean_is_exclusive(v___x_1212_)) as u8;
                    if v_isSharedCheck_1228_ == 0 {
                        v___x_1223_ = v___x_1212_;
                        v_isShared_1224_ = v_isSharedCheck_1228_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1221_);
                        lean_dec(v___x_1212_);
                        v___x_1223_ = lean_box(0);
                        v_isShared_1224_ = v_isSharedCheck_1228_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1216_ == 0 {
                    v___x_1218_ = v___x_1215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
                    v___x_1218_ = v_reuseFailAlloc_1219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1218_;
            }
            3 => {
                if v_isShared_1224_ == 0 {
                    v___x_1226_ = v___x_1223_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
                    v___x_1226_ = v_reuseFailAlloc_1227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg___boxed(
    mut v_es_1229_: *mut LeanObject,
    mut v_givenNames_1230_: *mut LeanObject,
    mut v_k_1231_: *mut LeanObject,
    mut v_config_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
    mut v___y_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1238_: *mut LeanObject = core::ptr::null_mut();
    v_res_1238_ =
        l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(
            v_es_1229_,
            v_givenNames_1230_,
            v_k_1231_,
            v_config_1232_,
            v___y_1233_,
            v___y_1234_,
            v___y_1235_,
            v___y_1236_,
        );
    lean_dec(v___y_1236_);
    lean_dec_ref(v___y_1235_);
    lean_dec(v___y_1234_);
    lean_dec_ref(v___y_1233_);
    lean_dec_ref(v_config_1232_);
    return v_res_1238_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(
    mut v_00_u03b1_1239_: *mut LeanObject,
    mut v_es_1240_: *mut LeanObject,
    mut v_givenNames_1241_: *mut LeanObject,
    mut v_k_1242_: *mut LeanObject,
    mut v_config_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    v___x_1249_ =
        l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(
            v_es_1240_,
            v_givenNames_1241_,
            v_k_1242_,
            v_config_1243_,
            v___y_1244_,
            v___y_1245_,
            v___y_1246_,
            v___y_1247_,
        );
    return v___x_1249_;
}
pub unsafe fn l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___boxed(
    mut v_00_u03b1_1250_: *mut LeanObject,
    mut v_es_1251_: *mut LeanObject,
    mut v_givenNames_1252_: *mut LeanObject,
    mut v_k_1253_: *mut LeanObject,
    mut v_config_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1260_: *mut LeanObject = core::ptr::null_mut();
    v_res_1260_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5(
        v_00_u03b1_1250_,
        v_es_1251_,
        v_givenNames_1252_,
        v_k_1253_,
        v_config_1254_,
        v___y_1255_,
        v___y_1256_,
        v___y_1257_,
        v___y_1258_,
    );
    lean_dec(v___y_1258_);
    lean_dec_ref(v___y_1257_);
    lean_dec(v___y_1256_);
    lean_dec_ref(v___y_1255_);
    lean_dec_ref(v_config_1254_);
    return v_res_1260_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(
    mut v_x_1261_: *mut LeanObject,
    mut v_x_1262_: *mut LeanObject,
    mut v_x_1263_: *mut LeanObject,
    mut v_x_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1269_: u8 = 0;
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1265_ = lean_ctor_get(v_x_1261_, 0);
                v_vs_1266_ = lean_ctor_get(v_x_1261_, 1);
                v_isSharedCheck_1290_ = (!lean_is_exclusive(v_x_1261_)) as u8;
                if v_isSharedCheck_1290_ == 0 {
                    v___x_1268_ = v_x_1261_;
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1266_);
                    lean_inc(v_ks_1265_);
                    lean_dec(v_x_1261_);
                    v___x_1268_ = lean_box(0);
                    v_isShared_1269_ = v_isSharedCheck_1290_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1270_ = lean_array_get_size(v_ks_1265_);
                v___x_1271_ = lean_nat_dec_lt(v_x_1262_, v___x_1270_);
                if v___x_1271_ == 0 {
                    lean_dec(v_x_1262_);
                    v___x_1272_ = lean_array_push(v_ks_1265_, v_x_1263_);
                    v___x_1273_ = lean_array_push(v_vs_1266_, v_x_1264_);
                    if v_isShared_1269_ == 0 {
                        lean_ctor_set(v___x_1268_, 1, v___x_1273_);
                        lean_ctor_set(v___x_1268_, 0, v___x_1272_);
                        v___x_1275_ = v___x_1268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1272_);
                        lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1273_);
                        v___x_1275_ = v_reuseFailAlloc_1276_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1277_ = lean_array_fget_borrowed(v_ks_1265_, v_x_1262_);
                    v___x_1278_ = l_Lean_instBEqMVarId_beq(v_x_1263_, v_k_x27_1277_);
                    if v___x_1278_ == 0 {
                        if v_isShared_1269_ == 0 {
                            v___x_1280_ = v___x_1268_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_ks_1265_);
                            lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_vs_1266_);
                            v___x_1280_ = v_reuseFailAlloc_1284_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1285_ = lean_array_fset(v_ks_1265_, v_x_1262_, v_x_1263_);
                        v___x_1286_ = lean_array_fset(v_vs_1266_, v_x_1262_, v_x_1264_);
                        lean_dec(v_x_1262_);
                        if v_isShared_1269_ == 0 {
                            lean_ctor_set(v___x_1268_, 1, v___x_1286_);
                            lean_ctor_set(v___x_1268_, 0, v___x_1285_);
                            v___x_1288_ = v___x_1268_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1285_);
                            lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1286_);
                            v___x_1288_ = v_reuseFailAlloc_1289_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1275_;
            }
            3 => {
                v___x_1281_ = lean_unsigned_to_nat(1);
                v___x_1282_ = lean_nat_add(v_x_1262_, v___x_1281_);
                lean_dec(v_x_1262_);
                v_x_1261_ = v___x_1280_;
                v_x_1262_ = v___x_1282_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(
    mut v_n_1291_: *mut LeanObject,
    mut v_k_1292_: *mut LeanObject,
    mut v_v_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = lean_unsigned_to_nat(0);
    v___x_1295_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_n_1291_, v___x_1294_, v_k_1292_, v_v_1293_);
    return v___x_1295_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0()
-> usize {
    let mut v___x_1296_: usize = 0;
    let mut v___x_1297_: usize = 0;
    let mut v___x_1298_: usize = 0;
    v___x_1296_ = 5usize;
    v___x_1297_ = 1usize;
    v___x_1298_ = lean_usize_shift_left(v___x_1297_, v___x_1296_);
    return v___x_1298_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1()
-> usize {
    let mut v___x_1299_: usize = 0;
    let mut v___x_1300_: usize = 0;
    let mut v___x_1301_: usize = 0;
    v___x_1299_ = 1usize;
    v___x_1300_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__0);
    v___x_1301_ = lean_usize_sub(v___x_1300_, v___x_1299_);
    return v___x_1301_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1302_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(
    mut v_x_1303_: *mut LeanObject,
    mut v_x_1304_: usize,
    mut v_x_1305_: usize,
    mut v_x_1306_: *mut LeanObject,
    mut v_x_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: usize = 0;
    let mut v___x_1310_: usize = 0;
    let mut v___x_1311_: usize = 0;
    let mut v___x_1312_: usize = 0;
    let mut v_j_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u8 = 0;
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v_v_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1339_: u8 = 0;
    let mut v_node_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1343_: u8 = 0;
    let mut v___x_1344_: usize = 0;
    let mut v___x_1345_: usize = 0;
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_unused_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1363_: u8 = 0;
    let mut v_ks_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: u8 = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v_reuseFailAlloc_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1303_) == 0 {
                    v_es_1308_ = lean_ctor_get(v_x_1303_, 0);
                    v___x_1309_ = 5usize;
                    v___x_1310_ = 1usize;
                    v___x_1311_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__1);
                    v___x_1312_ = lean_usize_land(v_x_1304_, v___x_1311_);
                    v_j_1313_ = lean_usize_to_nat(v___x_1312_);
                    v___x_1314_ = lean_array_get_size(v_es_1308_);
                    v___x_1315_ = lean_nat_dec_lt(v_j_1313_, v___x_1314_);
                    if v___x_1315_ == 0 {
                        lean_dec(v_j_1313_);
                        lean_dec(v_x_1307_);
                        lean_dec(v_x_1306_);
                        return v_x_1303_;
                    } else {
                        lean_inc_ref(v_es_1308_);
                        v_isSharedCheck_1352_ = (!lean_is_exclusive(v_x_1303_)) as u8;
                        if v_isSharedCheck_1352_ == 0 {
                            v_unused_1353_ = lean_ctor_get(v_x_1303_, 0);
                            lean_dec(v_unused_1353_);
                            v___x_1317_ = v_x_1303_;
                            v_isShared_1318_ = v_isSharedCheck_1352_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1303_);
                            v___x_1317_ = lean_box(0);
                            v_isShared_1318_ = v_isSharedCheck_1352_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1354_ = lean_ctor_get(v_x_1303_, 0);
                    v_vs_1355_ = lean_ctor_get(v_x_1303_, 1);
                    v_isSharedCheck_1375_ = (!lean_is_exclusive(v_x_1303_)) as u8;
                    if v_isSharedCheck_1375_ == 0 {
                        v___x_1357_ = v_x_1303_;
                        v_isShared_1358_ = v_isSharedCheck_1375_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1355_);
                        lean_inc(v_ks_1354_);
                        lean_dec(v_x_1303_);
                        v___x_1357_ = lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1375_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1319_ = lean_array_fget(v_es_1308_, v_j_1313_);
                v___x_1320_ = lean_box(0);
                v_xs_x27_1321_ = lean_array_fset(v_es_1308_, v_j_1313_, v___x_1320_);
                match lean_obj_tag(v_v_1319_) {
                    0 => {
                        v_key_1328_ = lean_ctor_get(v_v_1319_, 0);
                        v_val_1329_ = lean_ctor_get(v_v_1319_, 1);
                        v_isSharedCheck_1339_ = (!lean_is_exclusive(v_v_1319_)) as u8;
                        if v_isSharedCheck_1339_ == 0 {
                            v___x_1331_ = v_v_1319_;
                            v_isShared_1332_ = v_isSharedCheck_1339_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1329_);
                            lean_inc(v_key_1328_);
                            lean_dec(v_v_1319_);
                            v___x_1331_ = lean_box(0);
                            v_isShared_1332_ = v_isSharedCheck_1339_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1340_ = lean_ctor_get(v_v_1319_, 0);
                        v_isSharedCheck_1350_ = (!lean_is_exclusive(v_v_1319_)) as u8;
                        if v_isSharedCheck_1350_ == 0 {
                            v___x_1342_ = v_v_1319_;
                            v_isShared_1343_ = v_isSharedCheck_1350_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1340_);
                            lean_dec(v_v_1319_);
                            v___x_1342_ = lean_box(0);
                            v_isShared_1343_ = v_isSharedCheck_1350_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1351_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1351_, 0, v_x_1306_);
                        lean_ctor_set(v___x_1351_, 1, v_x_1307_);
                        v___y_1323_ = v___x_1351_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1324_ = lean_array_fset(v_xs_x27_1321_, v_j_1313_, v___y_1323_);
                lean_dec(v_j_1313_);
                if v_isShared_1318_ == 0 {
                    lean_ctor_set(v___x_1317_, 0, v___x_1324_);
                    v___x_1326_ = v___x_1317_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
                    v___x_1326_ = v_reuseFailAlloc_1327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1326_;
            }
            4 => {
                v___x_1333_ = l_Lean_instBEqMVarId_beq(v_x_1306_, v_key_1328_);
                if v___x_1333_ == 0 {
                    lean_del_object(v___x_1331_);
                    v___x_1334_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1328_,
                        v_val_1329_,
                        v_x_1306_,
                        v_x_1307_,
                    );
                    v___x_1335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1335_, 0, v___x_1334_);
                    v___y_1323_ = v___x_1335_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1329_);
                    lean_dec(v_key_1328_);
                    if v_isShared_1332_ == 0 {
                        lean_ctor_set(v___x_1331_, 1, v_x_1307_);
                        lean_ctor_set(v___x_1331_, 0, v_x_1306_);
                        v___x_1337_ = v___x_1331_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_x_1306_);
                        lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_x_1307_);
                        v___x_1337_ = v_reuseFailAlloc_1338_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1323_ = v___x_1337_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1344_ = lean_usize_shift_right(v_x_1304_, v___x_1309_);
                v___x_1345_ = lean_usize_add(v_x_1305_, v___x_1310_);
                v___x_1346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_node_1340_, v___x_1344_, v___x_1345_, v_x_1306_, v_x_1307_);
                if v_isShared_1343_ == 0 {
                    lean_ctor_set(v___x_1342_, 0, v___x_1346_);
                    v___x_1348_ = v___x_1342_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
                    v___x_1348_ = v_reuseFailAlloc_1349_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1323_ = v___x_1348_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1358_ == 0 {
                    v___x_1360_ = v___x_1357_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_ks_1354_);
                    lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_vs_1355_);
                    v___x_1360_ = v_reuseFailAlloc_1374_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1361_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v___x_1360_, v_x_1306_, v_x_1307_);
                v___x_1369_ = 7usize;
                v___x_1370_ = lean_usize_dec_le(v___x_1369_, v_x_1305_);
                if v___x_1370_ == 0 {
                    v___x_1371_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1361_);
                    v___x_1372_ = lean_unsigned_to_nat(4);
                    v___x_1373_ = lean_nat_dec_lt(v___x_1371_, v___x_1372_);
                    lean_dec(v___x_1371_);
                    v___y_1363_ = v___x_1373_;
                    state = 10;
                    continue;
                } else {
                    v___y_1363_ = v___x_1370_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1363_ == 0 {
                    v_ks_1364_ = lean_ctor_get(v_newNode_1361_, 0);
                    lean_inc_ref(v_ks_1364_);
                    v_vs_1365_ = lean_ctor_get(v_newNode_1361_, 1);
                    lean_inc_ref(v_vs_1365_);
                    lean_dec_ref(v_newNode_1361_);
                    v___x_1366_ = lean_unsigned_to_nat(0);
                    v___x_1367_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___closed__2);
                    v___x_1368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_x_1305_, v_ks_1364_, v_vs_1365_, v___x_1366_, v___x_1367_);
                    lean_dec_ref(v_vs_1365_);
                    lean_dec_ref(v_ks_1364_);
                    return v___x_1368_;
                } else {
                    return v_newNode_1361_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(
    mut v_depth_1376_: usize,
    mut v_keys_1377_: *mut LeanObject,
    mut v_vals_1378_: *mut LeanObject,
    mut v_i_1379_: *mut LeanObject,
    mut v_entries_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v_k_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: u64 = 0;
    let mut v_h_1386_: usize = 0;
    let mut v___x_1387_: usize = 0;
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: usize = 0;
    let mut v___x_1390_: usize = 0;
    let mut v___x_1391_: usize = 0;
    let mut v_h_1392_: usize = 0;
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1381_ = lean_array_get_size(v_keys_1377_);
                v___x_1382_ = lean_nat_dec_lt(v_i_1379_, v___x_1381_);
                if v___x_1382_ == 0 {
                    lean_dec(v_i_1379_);
                    return v_entries_1380_;
                } else {
                    v_k_1383_ = lean_array_fget_borrowed(v_keys_1377_, v_i_1379_);
                    v_v_1384_ = lean_array_fget_borrowed(v_vals_1378_, v_i_1379_);
                    v___x_1385_ = l_Lean_instHashableMVarId_hash(v_k_1383_);
                    v_h_1386_ = lean_uint64_to_usize(v___x_1385_);
                    v___x_1387_ = 5usize;
                    v___x_1388_ = lean_unsigned_to_nat(1);
                    v___x_1389_ = 1usize;
                    v___x_1390_ = lean_usize_sub(v_depth_1376_, v___x_1389_);
                    v___x_1391_ = lean_usize_mul(v___x_1387_, v___x_1390_);
                    v_h_1392_ = lean_usize_shift_right(v_h_1386_, v___x_1391_);
                    v___x_1393_ = lean_nat_add(v_i_1379_, v___x_1388_);
                    lean_dec(v_i_1379_);
                    lean_inc(v_v_1384_);
                    lean_inc(v_k_1383_);
                    v___x_1394_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_entries_1380_, v_h_1392_, v_depth_1376_, v_k_1383_, v_v_1384_);
                    v_i_1379_ = v___x_1393_;
                    v_entries_1380_ = v___x_1394_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg___boxed(
    mut v_depth_1396_: *mut LeanObject,
    mut v_keys_1397_: *mut LeanObject,
    mut v_vals_1398_: *mut LeanObject,
    mut v_i_1399_: *mut LeanObject,
    mut v_entries_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1401_: usize = 0;
    let mut v_res_1402_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1401_ = lean_unbox_usize(v_depth_1396_);
    lean_dec(v_depth_1396_);
    v_res_1402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_boxed_1401_, v_keys_1397_, v_vals_1398_, v_i_1399_, v_entries_1400_);
    lean_dec_ref(v_vals_1398_);
    lean_dec_ref(v_keys_1397_);
    return v_res_1402_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg___boxed(
    mut v_x_1403_: *mut LeanObject,
    mut v_x_1404_: *mut LeanObject,
    mut v_x_1405_: *mut LeanObject,
    mut v_x_1406_: *mut LeanObject,
    mut v_x_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6152__boxed_1408_: usize = 0;
    let mut v_x_6153__boxed_1409_: usize = 0;
    let mut v_res_1410_: *mut LeanObject = core::ptr::null_mut();
    v_x_6152__boxed_1408_ = lean_unbox_usize(v_x_1404_);
    lean_dec(v_x_1404_);
    v_x_6153__boxed_1409_ = lean_unbox_usize(v_x_1405_);
    lean_dec(v_x_1405_);
    v_res_1410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1403_, v_x_6152__boxed_1408_, v_x_6153__boxed_1409_, v_x_1406_, v_x_1407_);
    return v_res_1410_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(
    mut v_x_1411_: *mut LeanObject,
    mut v_x_1412_: *mut LeanObject,
    mut v_x_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1414_: u64 = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1414_ = l_Lean_instHashableMVarId_hash(v_x_1412_);
    v___x_1415_ = lean_uint64_to_usize(v___x_1414_);
    v___x_1416_ = 1usize;
    v___x_1417_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1411_, v___x_1415_, v___x_1416_, v_x_1412_, v_x_1413_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
    mut v_mvarId_1418_: *mut LeanObject,
    mut v_val_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v_depth_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1454_: u8 = 0;
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1422_ = lean_st_ref_take(v___y_1420_);
                v_mctx_1423_ = lean_ctor_get(v___x_1422_, 0);
                v_cache_1424_ = lean_ctor_get(v___x_1422_, 1);
                v_zetaDeltaFVarIds_1425_ = lean_ctor_get(v___x_1422_, 2);
                v_postponed_1426_ = lean_ctor_get(v___x_1422_, 3);
                v_diag_1427_ = lean_ctor_get(v___x_1422_, 4);
                v_isSharedCheck_1455_ = (!lean_is_exclusive(v___x_1422_)) as u8;
                if v_isSharedCheck_1455_ == 0 {
                    v___x_1429_ = v___x_1422_;
                    v_isShared_1430_ = v_isSharedCheck_1455_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1427_);
                    lean_inc(v_postponed_1426_);
                    lean_inc(v_zetaDeltaFVarIds_1425_);
                    lean_inc(v_cache_1424_);
                    lean_inc(v_mctx_1423_);
                    lean_dec(v___x_1422_);
                    v___x_1429_ = lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1455_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1431_ = lean_ctor_get(v_mctx_1423_, 0);
                v_levelAssignDepth_1432_ = lean_ctor_get(v_mctx_1423_, 1);
                v_lmvarCounter_1433_ = lean_ctor_get(v_mctx_1423_, 2);
                v_mvarCounter_1434_ = lean_ctor_get(v_mctx_1423_, 3);
                v_lDecls_1435_ = lean_ctor_get(v_mctx_1423_, 4);
                v_decls_1436_ = lean_ctor_get(v_mctx_1423_, 5);
                v_userNames_1437_ = lean_ctor_get(v_mctx_1423_, 6);
                v_lAssignment_1438_ = lean_ctor_get(v_mctx_1423_, 7);
                v_eAssignment_1439_ = lean_ctor_get(v_mctx_1423_, 8);
                v_dAssignment_1440_ = lean_ctor_get(v_mctx_1423_, 9);
                v_isSharedCheck_1454_ = (!lean_is_exclusive(v_mctx_1423_)) as u8;
                if v_isSharedCheck_1454_ == 0 {
                    v___x_1442_ = v_mctx_1423_;
                    v_isShared_1443_ = v_isSharedCheck_1454_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1440_);
                    lean_inc(v_eAssignment_1439_);
                    lean_inc(v_lAssignment_1438_);
                    lean_inc(v_userNames_1437_);
                    lean_inc(v_decls_1436_);
                    lean_inc(v_lDecls_1435_);
                    lean_inc(v_mvarCounter_1434_);
                    lean_inc(v_lmvarCounter_1433_);
                    lean_inc(v_levelAssignDepth_1432_);
                    lean_inc(v_depth_1431_);
                    lean_dec(v_mctx_1423_);
                    v___x_1442_ = lean_box(0);
                    v_isShared_1443_ = v_isSharedCheck_1454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1444_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_eAssignment_1439_, v_mvarId_1418_, v_val_1419_);
                if v_isShared_1443_ == 0 {
                    lean_ctor_set(v___x_1442_, 8, v___x_1444_);
                    v___x_1446_ = v___x_1442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_depth_1431_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_levelAssignDepth_1432_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_lmvarCounter_1433_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_mvarCounter_1434_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_lDecls_1435_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 5, v_decls_1436_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 6, v_userNames_1437_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 7, v_lAssignment_1438_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 8, v___x_1444_);
                    lean_ctor_set(v_reuseFailAlloc_1453_, 9, v_dAssignment_1440_);
                    v___x_1446_ = v_reuseFailAlloc_1453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1430_ == 0 {
                    lean_ctor_set(v___x_1429_, 0, v___x_1446_);
                    v___x_1448_ = v___x_1429_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_cache_1424_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_zetaDeltaFVarIds_1425_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_postponed_1426_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_diag_1427_);
                    v___x_1448_ = v_reuseFailAlloc_1452_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1449_ = lean_st_ref_set(v___y_1420_, v___x_1448_);
                v___x_1450_ = lean_box(0);
                v___x_1451_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1451_, 0, v___x_1450_);
                return v___x_1451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg___boxed(
    mut v_mvarId_1456_: *mut LeanObject,
    mut v_val_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1460_: *mut LeanObject = core::ptr::null_mut();
    v_res_1460_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
            v_mvarId_1456_,
            v_val_1457_,
            v___y_1458_,
        );
    lean_dec(v___y_1458_);
    return v_res_1460_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1() -> *mut LeanObject
{
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1462_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__0;
    v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2() -> *mut LeanObject
{
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__1,
    );
    v___x_1465_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1465_, 0, v___x_1464_);
    return v___x_1465_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(
    mut v___x_1466_: *mut LeanObject,
    mut v_a_1467_: *mut LeanObject,
    mut v___x_1468_: *mut LeanObject,
    mut v_a_1469_: *mut LeanObject,
    mut v_mvar_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
    mut v___y_1473_: *mut LeanObject,
    mut v___y_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1486_: u8 = 0;
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_1467_);
                v___x_1476_ = l_Lean_Meta_isExprDefEq(
                    v___x_1466_,
                    v_a_1467_,
                    v___y_1471_,
                    v___y_1472_,
                    v___y_1473_,
                    v___y_1474_,
                );
                if lean_obj_tag(v___x_1476_) == 0 {
                    v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
                    lean_inc(v_a_1477_);
                    lean_dec_ref_known(v___x_1476_, 1);
                    v___x_1478_ = (lean_unbox(v_a_1477_) as u8);
                    lean_dec(v_a_1477_);
                    if v___x_1478_ == 0 {
                        v___x_1479_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___closed__2,
                        );
                        v___x_1480_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_1468_,
                            v_a_1469_,
                            v___x_1479_,
                            v___y_1471_,
                            v___y_1472_,
                            v___y_1473_,
                            v___y_1474_,
                        );
                        if lean_obj_tag(v___x_1480_) == 0 {
                            lean_dec_ref_known(v___x_1480_, 1);
                            v___x_1481_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_1470_, v_a_1467_, v___y_1472_);
                            return v___x_1481_;
                        } else {
                            lean_dec(v_mvar_1470_);
                            lean_dec_ref(v_a_1467_);
                            return v___x_1480_;
                        }
                    } else {
                        lean_dec(v_a_1469_);
                        lean_dec(v___x_1468_);
                        v___x_1482_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(v_mvar_1470_, v_a_1467_, v___y_1472_);
                        return v___x_1482_;
                    }
                } else {
                    lean_dec(v_mvar_1470_);
                    lean_dec(v_a_1469_);
                    lean_dec(v___x_1468_);
                    lean_dec_ref(v_a_1467_);
                    v_a_1483_ = lean_ctor_get(v___x_1476_, 0);
                    v_isSharedCheck_1490_ = (!lean_is_exclusive(v___x_1476_)) as u8;
                    if v_isSharedCheck_1490_ == 0 {
                        v___x_1485_ = v___x_1476_;
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1483_);
                        lean_dec(v___x_1476_);
                        v___x_1485_ = lean_box(0);
                        v_isShared_1486_ = v_isSharedCheck_1490_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1486_ == 0 {
                    v___x_1488_ = v___x_1485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed(
    mut v___x_1491_: *mut LeanObject,
    mut v_a_1492_: *mut LeanObject,
    mut v___x_1493_: *mut LeanObject,
    mut v_a_1494_: *mut LeanObject,
    mut v_mvar_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
    mut v___y_1500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1501_: *mut LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0(
        v___x_1491_,
        v_a_1492_,
        v___x_1493_,
        v_a_1494_,
        v_mvar_1495_,
        v___y_1496_,
        v___y_1497_,
        v___y_1498_,
        v___y_1499_,
    );
    lean_dec(v___y_1499_);
    lean_dec_ref(v___y_1498_);
    lean_dec(v___y_1497_);
    lean_dec_ref(v___y_1496_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
    mut v___x_1502_: *mut LeanObject,
    mut v___x_1503_: u8,
    mut v___x_1504_: u8,
    mut v___x_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_mvar_1507_: *mut LeanObject,
    mut v_e_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
    mut v___y_1510_: *mut LeanObject,
    mut v___y_1511_: *mut LeanObject,
    mut v___y_1512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1514_ = 1;
                v___x_1515_ = l_Lean_Meta_mkLetFVars(
                    v___x_1502_,
                    v_e_1508_,
                    v___x_1503_,
                    v___x_1504_,
                    v___x_1514_,
                    v___y_1509_,
                    v___y_1510_,
                    v___y_1511_,
                    v___y_1512_,
                );
                if lean_obj_tag(v___x_1515_) == 0 {
                    v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
                    lean_inc(v_a_1516_);
                    lean_dec_ref_known(v___x_1515_, 1);
                    lean_inc_n(v_mvar_1507_, 2);
                    v___x_1517_ = l_Lean_Expr_mvar___override(v_mvar_1507_);
                    v___f_1518_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        5,
                    );
                    lean_closure_set(v___f_1518_, 0, v___x_1517_);
                    lean_closure_set(v___f_1518_, 1, v_a_1516_);
                    lean_closure_set(v___f_1518_, 2, v___x_1505_);
                    lean_closure_set(v___f_1518_, 3, v_a_1506_);
                    lean_closure_set(v___f_1518_, 4, v_mvar_1507_);
                    v___x_1519_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__4___redArg(v_mvar_1507_, v___f_1518_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
                    return v___x_1519_;
                } else {
                    lean_dec(v_mvar_1507_);
                    lean_dec(v_a_1506_);
                    lean_dec(v___x_1505_);
                    v_a_1520_ = lean_ctor_get(v___x_1515_, 0);
                    v_isSharedCheck_1527_ = (!lean_is_exclusive(v___x_1515_)) as u8;
                    if v_isSharedCheck_1527_ == 0 {
                        v___x_1522_ = v___x_1515_;
                        v_isShared_1523_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1520_);
                        lean_dec(v___x_1515_);
                        v___x_1522_ = lean_box(0);
                        v_isShared_1523_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1523_ == 0 {
                    v___x_1525_ = v___x_1522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
                    v___x_1525_ = v_reuseFailAlloc_1526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1___boxed(
    mut v___x_1528_: *mut LeanObject,
    mut v___x_1529_: *mut LeanObject,
    mut v___x_1530_: *mut LeanObject,
    mut v___x_1531_: *mut LeanObject,
    mut v_a_1532_: *mut LeanObject,
    mut v_mvar_1533_: *mut LeanObject,
    mut v_e_1534_: *mut LeanObject,
    mut v___y_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
    mut v___y_1537_: *mut LeanObject,
    mut v___y_1538_: *mut LeanObject,
    mut v___y_1539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6446__boxed_1540_: u8 = 0;
    let mut v___x_6447__boxed_1541_: u8 = 0;
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v___x_6446__boxed_1540_ = (lean_unbox(v___x_1529_) as u8);
    v___x_6447__boxed_1541_ = (lean_unbox(v___x_1530_) as u8);
    v_res_1542_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
        v___x_1528_,
        v___x_6446__boxed_1540_,
        v___x_6447__boxed_1541_,
        v___x_1531_,
        v_a_1532_,
        v_mvar_1533_,
        v_e_1534_,
        v___y_1535_,
        v___y_1536_,
        v___y_1537_,
        v___y_1538_,
    );
    lean_dec(v___y_1538_);
    lean_dec_ref(v___y_1537_);
    lean_dec(v___y_1536_);
    lean_dec_ref(v___y_1535_);
    lean_dec_ref(v___x_1528_);
    return v_res_1542_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(
    mut v_sz_1543_: usize,
    mut v_i_1544_: usize,
    mut v_bs_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1546_: u8 = 0;
    let mut v_v_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: usize = 0;
    let mut v___x_1552_: usize = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1546_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
                if v___x_1546_ == 0 {
                    return v_bs_1545_;
                } else {
                    v_v_1547_ = lean_array_uget(v_bs_1545_, v_i_1544_);
                    v___x_1548_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1549_ = lean_array_uset(v_bs_1545_, v_i_1544_, v___x_1548_);
                    v___x_1550_ = l_Lean_Expr_fvar___override(v_v_1547_);
                    v___x_1551_ = 1usize;
                    v___x_1552_ = lean_usize_add(v_i_1544_, v___x_1551_);
                    v___x_1553_ = lean_array_uset(v_bs_x27_1549_, v_i_1544_, v___x_1550_);
                    v_i_1544_ = v___x_1552_;
                    v_bs_1545_ = v___x_1553_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2___boxed(
    mut v_sz_1555_: *mut LeanObject,
    mut v_i_1556_: *mut LeanObject,
    mut v_bs_1557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1558_: usize = 0;
    let mut v_i_boxed_1559_: usize = 0;
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1558_ = lean_unbox_usize(v_sz_1555_);
    lean_dec(v_sz_1555_);
    v_i_boxed_1559_ = lean_unbox_usize(v_i_1556_);
    lean_dec(v_i_1556_);
    v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_boxed_1558_, v_i_boxed_1559_, v_bs_1557_);
    return v_res_1560_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1() -> *mut LeanObject
{
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    v___x_1562_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__0;
    v___x_1563_ = l_Lean_stringToMessageData(v___x_1562_);
    return v___x_1563_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2() -> *mut LeanObject
{
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    v___x_1564_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__1,
    );
    v___x_1565_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1565_, 0, v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(
    mut v___x_1566_: *mut LeanObject,
    mut v_a_1567_: *mut LeanObject,
    mut v___x_1568_: usize,
    mut v___x_1569_: u8,
    mut v___x_1570_: u8,
    mut v___x_1571_: *mut LeanObject,
    mut v_snd_1572_: *mut LeanObject,
    mut v_fst_1573_: *mut LeanObject,
    mut v_fvarIds_1574_: *mut LeanObject,
    mut v_es_1575_: *mut LeanObject,
    mut v_x_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
    mut v___y_1578_: *mut LeanObject,
    mut v___y_1579_: *mut LeanObject,
    mut v___y_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v_sz_1594_: usize = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1601_: u8 = 0;
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1611_: u8 = 0;
    let mut v_unused_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut v_a_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1624_: u8 = 0;
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_a_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1637_: u8 = 0;
    let mut v_a_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1641_: u8 = 0;
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = l_Lean_instInhabitedExpr;
                v___x_1583_ = lean_array_get_borrowed(v___x_1582_, v_es_1575_, v___x_1566_);
                v___x_1646_ = lean_array_get_size(v_fvarIds_1574_);
                v___x_1647_ = lean_nat_dec_eq(v___x_1646_, v___x_1566_);
                if v___x_1647_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1648_ = lean_expr_eqv(v_fst_1573_, v___x_1583_);
                    if v___x_1648_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1649_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2,
                        );
                        lean_inc(v_a_1567_);
                        lean_inc(v___x_1571_);
                        v___x_1650_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_1571_,
                            v_a_1567_,
                            v___x_1649_,
                            v___y_1577_,
                            v___y_1578_,
                            v___y_1579_,
                            v___y_1580_,
                        );
                        if lean_obj_tag(v___x_1650_) == 0 {
                            lean_dec_ref_known(v___x_1650_, 1);
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_fvarIds_1574_);
                            lean_dec_ref(v_snd_1572_);
                            lean_dec(v___x_1571_);
                            lean_dec(v_a_1567_);
                            v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
                            v_isSharedCheck_1658_ = (!lean_is_exclusive(v___x_1650_)) as u8;
                            if v_isSharedCheck_1658_ == 0 {
                                v___x_1653_ = v___x_1650_;
                                v_isShared_1654_ = v_isSharedCheck_1658_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_1651_);
                                lean_dec(v___x_1650_);
                                v___x_1653_ = lean_box(0);
                                v_isShared_1654_ = v_isSharedCheck_1658_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_1567_);
                v___x_1585_ = l_Lean_MVarId_getTag(
                    v_a_1567_,
                    v___y_1577_,
                    v___y_1578_,
                    v___y_1579_,
                    v___y_1580_,
                );
                if lean_obj_tag(v___x_1585_) == 0 {
                    v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
                    lean_inc(v_a_1586_);
                    lean_dec_ref_known(v___x_1585_, 1);
                    lean_inc(v___x_1583_);
                    v___x_1587_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
                        v___x_1583_,
                        v_a_1586_,
                        v___y_1577_,
                        v___y_1578_,
                        v___y_1579_,
                        v___y_1580_,
                    );
                    if lean_obj_tag(v___x_1587_) == 0 {
                        v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
                        lean_inc(v_a_1588_);
                        lean_dec_ref_known(v___x_1587_, 1);
                        v_fst_1589_ = lean_ctor_get(v_a_1588_, 0);
                        v_snd_1590_ = lean_ctor_get(v_a_1588_, 1);
                        v_isSharedCheck_1629_ = (!lean_is_exclusive(v_a_1588_)) as u8;
                        if v_isSharedCheck_1629_ == 0 {
                            v___x_1592_ = v_a_1588_;
                            v_isShared_1593_ = v_isSharedCheck_1629_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_1590_);
                            lean_inc(v_fst_1589_);
                            lean_dec(v_a_1588_);
                            v___x_1592_ = lean_box(0);
                            v_isShared_1593_ = v_isSharedCheck_1629_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_fvarIds_1574_);
                        lean_dec_ref(v_snd_1572_);
                        lean_dec(v___x_1571_);
                        lean_dec(v_a_1567_);
                        v_a_1630_ = lean_ctor_get(v___x_1587_, 0);
                        v_isSharedCheck_1637_ = (!lean_is_exclusive(v___x_1587_)) as u8;
                        if v_isSharedCheck_1637_ == 0 {
                            v___x_1632_ = v___x_1587_;
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1630_);
                            lean_dec(v___x_1587_);
                            v___x_1632_ = lean_box(0);
                            v_isShared_1633_ = v_isSharedCheck_1637_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fvarIds_1574_);
                    lean_dec_ref(v_snd_1572_);
                    lean_dec(v___x_1571_);
                    lean_dec(v_a_1567_);
                    v_a_1638_ = lean_ctor_get(v___x_1585_, 0);
                    v_isSharedCheck_1645_ = (!lean_is_exclusive(v___x_1585_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1640_ = v___x_1585_;
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1638_);
                        lean_dec(v___x_1585_);
                        v___x_1640_ = lean_box(0);
                        v_isShared_1641_ = v_isSharedCheck_1645_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_sz_1594_ = lean_array_size(v_fvarIds_1574_);
                lean_inc_ref(v_fvarIds_1574_);
                v___x_1595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__2(v_sz_1594_, v___x_1568_, v_fvarIds_1574_);
                v___x_1596_ = l_Lean_Expr_mvarId_x21(v_fst_1589_);
                lean_dec(v_fst_1589_);
                lean_inc(v_a_1567_);
                lean_inc(v___x_1571_);
                v___x_1597_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
                    v___x_1595_,
                    v___x_1569_,
                    v___x_1570_,
                    v___x_1571_,
                    v_a_1567_,
                    v___x_1596_,
                    v_snd_1572_,
                    v___y_1577_,
                    v___y_1578_,
                    v___y_1579_,
                    v___y_1580_,
                );
                if lean_obj_tag(v___x_1597_) == 0 {
                    lean_dec_ref_known(v___x_1597_, 1);
                    lean_inc(v_snd_1590_);
                    lean_inc(v_a_1567_);
                    v___x_1598_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__1(
                        v___x_1595_,
                        v___x_1569_,
                        v___x_1570_,
                        v___x_1571_,
                        v_a_1567_,
                        v_a_1567_,
                        v_snd_1590_,
                        v___y_1577_,
                        v___y_1578_,
                        v___y_1579_,
                        v___y_1580_,
                    );
                    lean_dec_ref(v___x_1595_);
                    if lean_obj_tag(v___x_1598_) == 0 {
                        v_isSharedCheck_1611_ = (!lean_is_exclusive(v___x_1598_)) as u8;
                        if v_isSharedCheck_1611_ == 0 {
                            v_unused_1612_ = lean_ctor_get(v___x_1598_, 0);
                            lean_dec(v_unused_1612_);
                            v___x_1600_ = v___x_1598_;
                            v_isShared_1601_ = v_isSharedCheck_1611_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_1598_);
                            v___x_1600_ = lean_box(0);
                            v_isShared_1601_ = v_isSharedCheck_1611_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_1592_);
                        lean_dec(v_snd_1590_);
                        lean_dec_ref(v_fvarIds_1574_);
                        v_a_1613_ = lean_ctor_get(v___x_1598_, 0);
                        v_isSharedCheck_1620_ = (!lean_is_exclusive(v___x_1598_)) as u8;
                        if v_isSharedCheck_1620_ == 0 {
                            v___x_1615_ = v___x_1598_;
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1613_);
                            lean_dec(v___x_1598_);
                            v___x_1615_ = lean_box(0);
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1595_);
                    lean_del_object(v___x_1592_);
                    lean_dec(v_snd_1590_);
                    lean_dec_ref(v_fvarIds_1574_);
                    lean_dec(v___x_1571_);
                    lean_dec(v_a_1567_);
                    v_a_1621_ = lean_ctor_get(v___x_1597_, 0);
                    v_isSharedCheck_1628_ = (!lean_is_exclusive(v___x_1597_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1597_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1621_);
                        lean_dec(v___x_1597_);
                        v___x_1623_ = lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1602_ = l_Lean_Expr_mvarId_x21(v_snd_1590_);
                lean_dec(v_snd_1590_);
                v___x_1603_ = lean_box(0);
                v___x_1604_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1604_, 0, v___x_1602_);
                lean_ctor_set(v___x_1604_, 1, v___x_1603_);
                if v_isShared_1593_ == 0 {
                    lean_ctor_set(v___x_1592_, 1, v___x_1604_);
                    lean_ctor_set(v___x_1592_, 0, v_fvarIds_1574_);
                    v___x_1606_ = v___x_1592_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_fvarIds_1574_);
                    lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1604_);
                    v___x_1606_ = v_reuseFailAlloc_1610_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1601_ == 0 {
                    lean_ctor_set(v___x_1600_, 0, v___x_1606_);
                    v___x_1608_ = v___x_1600_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
                    v___x_1608_ = v_reuseFailAlloc_1609_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1608_;
            }
            6 => {
                if v_isShared_1616_ == 0 {
                    v___x_1618_ = v___x_1615_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1618_;
            }
            8 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1626_;
            }
            10 => {
                if v_isShared_1633_ == 0 {
                    v___x_1635_ = v___x_1632_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1630_);
                    v___x_1635_ = v_reuseFailAlloc_1636_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1635_;
            }
            12 => {
                if v_isShared_1641_ == 0 {
                    v___x_1643_ = v___x_1640_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
                    v___x_1643_ = v_reuseFailAlloc_1644_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1643_;
            }
            14 => {
                if v_isShared_1654_ == 0 {
                    v___x_1656_ = v___x_1653_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
                    v___x_1656_ = v_reuseFailAlloc_1657_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed(
    mut v___x_1659_: *mut LeanObject,
    mut v_a_1660_: *mut LeanObject,
    mut v___x_1661_: *mut LeanObject,
    mut v___x_1662_: *mut LeanObject,
    mut v___x_1663_: *mut LeanObject,
    mut v___x_1664_: *mut LeanObject,
    mut v_snd_1665_: *mut LeanObject,
    mut v_fst_1666_: *mut LeanObject,
    mut v_fvarIds_1667_: *mut LeanObject,
    mut v_es_1668_: *mut LeanObject,
    mut v_x_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6529__boxed_1675_: usize = 0;
    let mut v___x_6530__boxed_1676_: u8 = 0;
    let mut v___x_6531__boxed_1677_: u8 = 0;
    let mut v_res_1678_: *mut LeanObject = core::ptr::null_mut();
    v___x_6529__boxed_1675_ = lean_unbox_usize(v___x_1661_);
    lean_dec(v___x_1661_);
    v___x_6530__boxed_1676_ = (lean_unbox(v___x_1662_) as u8);
    v___x_6531__boxed_1677_ = (lean_unbox(v___x_1663_) as u8);
    v_res_1678_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2(
        v___x_1659_,
        v_a_1660_,
        v___x_6529__boxed_1675_,
        v___x_6530__boxed_1676_,
        v___x_6531__boxed_1677_,
        v___x_1664_,
        v_snd_1665_,
        v_fst_1666_,
        v_fvarIds_1667_,
        v_es_1668_,
        v_x_1669_,
        v___y_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
    );
    lean_dec(v___y_1673_);
    lean_dec_ref(v___y_1672_);
    lean_dec(v___y_1671_);
    lean_dec_ref(v___y_1670_);
    lean_dec(v_x_1669_);
    lean_dec_ref(v_es_1668_);
    lean_dec_ref(v_fst_1666_);
    lean_dec(v___x_1659_);
    return v_res_1678_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(
    mut v___x_1682_: *mut LeanObject,
    mut v___x_1683_: usize,
    mut v___x_1684_: u8,
    mut v___x_1685_: u8,
    mut v_snd_1686_: *mut LeanObject,
    mut v_fst_1687_: *mut LeanObject,
    mut v___x_1688_: *mut LeanObject,
    mut v___x_1689_: *mut LeanObject,
    mut v_a_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut v_unused_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1726_: u8 = 0;
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1730_: u8 = 0;
    let mut v_a_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_a_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_a_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1700_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_1692_,
                    v___y_1695_,
                    v___y_1696_,
                    v___y_1697_,
                    v___y_1698_,
                );
                if lean_obj_tag(v___x_1700_) == 0 {
                    v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
                    lean_inc_n(v_a_1701_, 2);
                    lean_dec_ref_known(v___x_1700_, 1);
                    v___x_1702_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___closed__1;
                    v___x_1703_ = l_Lean_MVarId_checkNotAssigned(
                        v_a_1701_,
                        v___x_1702_,
                        v___y_1695_,
                        v___y_1696_,
                        v___y_1697_,
                        v___y_1698_,
                    );
                    if lean_obj_tag(v___x_1703_) == 0 {
                        lean_dec_ref_known(v___x_1703_, 1);
                        v___x_1704_ = lean_box_usize(v___x_1683_);
                        v___x_1705_ = lean_box((v___x_1684_) as usize);
                        v___x_1706_ = lean_box((v___x_1685_) as usize);
                        lean_inc_ref(v_fst_1687_);
                        v___f_1707_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___boxed
                                as *mut core::ffi::c_void,
                            16,
                            8,
                        );
                        lean_closure_set(v___f_1707_, 0, v___x_1682_);
                        lean_closure_set(v___f_1707_, 1, v_a_1701_);
                        lean_closure_set(v___f_1707_, 2, v___x_1704_);
                        lean_closure_set(v___f_1707_, 3, v___x_1705_);
                        lean_closure_set(v___f_1707_, 4, v___x_1706_);
                        lean_closure_set(v___f_1707_, 5, v___x_1702_);
                        lean_closure_set(v___f_1707_, 6, v_snd_1686_);
                        lean_closure_set(v___f_1707_, 7, v_fst_1687_);
                        v___x_1708_ = lean_mk_empty_array_with_capacity(v___x_1688_);
                        v___x_1709_ = lean_array_push(v___x_1708_, v_fst_1687_);
                        v___x_1710_ = l_Lean_Meta_extractLets___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__5___redArg(v___x_1709_, v___x_1689_, v___f_1707_, v_a_1690_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
                        if lean_obj_tag(v___x_1710_) == 0 {
                            v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
                            lean_inc(v_a_1711_);
                            lean_dec_ref_known(v___x_1710_, 1);
                            v_fst_1712_ = lean_ctor_get(v_a_1711_, 0);
                            lean_inc(v_fst_1712_);
                            v_snd_1713_ = lean_ctor_get(v_a_1711_, 1);
                            lean_inc(v_snd_1713_);
                            lean_dec(v_a_1711_);
                            v___x_1714_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v_snd_1713_,
                                v___y_1692_,
                                v___y_1695_,
                                v___y_1696_,
                                v___y_1697_,
                                v___y_1698_,
                            );
                            if lean_obj_tag(v___x_1714_) == 0 {
                                v_isSharedCheck_1721_ = (!lean_is_exclusive(v___x_1714_)) as u8;
                                if v_isSharedCheck_1721_ == 0 {
                                    v_unused_1722_ = lean_ctor_get(v___x_1714_, 0);
                                    lean_dec(v_unused_1722_);
                                    v___x_1716_ = v___x_1714_;
                                    v_isShared_1717_ = v_isSharedCheck_1721_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___x_1714_);
                                    v___x_1716_ = lean_box(0);
                                    v_isShared_1717_ = v_isSharedCheck_1721_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_fst_1712_);
                                v_a_1723_ = lean_ctor_get(v___x_1714_, 0);
                                v_isSharedCheck_1730_ = (!lean_is_exclusive(v___x_1714_)) as u8;
                                if v_isSharedCheck_1730_ == 0 {
                                    v___x_1725_ = v___x_1714_;
                                    v_isShared_1726_ = v_isSharedCheck_1730_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1723_);
                                    lean_dec(v___x_1714_);
                                    v___x_1725_ = lean_box(0);
                                    v_isShared_1726_ = v_isSharedCheck_1730_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1731_ = lean_ctor_get(v___x_1710_, 0);
                            v_isSharedCheck_1738_ = (!lean_is_exclusive(v___x_1710_)) as u8;
                            if v_isSharedCheck_1738_ == 0 {
                                v___x_1733_ = v___x_1710_;
                                v_isShared_1734_ = v_isSharedCheck_1738_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1731_);
                                lean_dec(v___x_1710_);
                                v___x_1733_ = lean_box(0);
                                v_isShared_1734_ = v_isSharedCheck_1738_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1701_);
                        lean_dec(v___x_1689_);
                        lean_dec_ref(v_fst_1687_);
                        lean_dec_ref(v_snd_1686_);
                        lean_dec(v___x_1682_);
                        v_a_1739_ = lean_ctor_get(v___x_1703_, 0);
                        v_isSharedCheck_1746_ = (!lean_is_exclusive(v___x_1703_)) as u8;
                        if v_isSharedCheck_1746_ == 0 {
                            v___x_1741_ = v___x_1703_;
                            v_isShared_1742_ = v_isSharedCheck_1746_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1739_);
                            lean_dec(v___x_1703_);
                            v___x_1741_ = lean_box(0);
                            v_isShared_1742_ = v_isSharedCheck_1746_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1689_);
                    lean_dec_ref(v_fst_1687_);
                    lean_dec_ref(v_snd_1686_);
                    lean_dec(v___x_1682_);
                    v_a_1747_ = lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1754_ = (!lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1754_ == 0 {
                        v___x_1749_ = v___x_1700_;
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1747_);
                        lean_dec(v___x_1700_);
                        v___x_1749_ = lean_box(0);
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1717_ == 0 {
                    lean_ctor_set(v___x_1716_, 0, v_fst_1712_);
                    v___x_1719_ = v___x_1716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_fst_1712_);
                    v___x_1719_ = v_reuseFailAlloc_1720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1719_;
            }
            3 => {
                if v_isShared_1726_ == 0 {
                    v___x_1728_ = v___x_1725_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
                    v___x_1728_ = v_reuseFailAlloc_1729_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1728_;
            }
            5 => {
                if v_isShared_1734_ == 0 {
                    v___x_1736_ = v___x_1733_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
                    v___x_1736_ = v_reuseFailAlloc_1737_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1736_;
            }
            7 => {
                if v_isShared_1742_ == 0 {
                    v___x_1744_ = v___x_1741_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
                    v___x_1744_ = v_reuseFailAlloc_1745_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1744_;
            }
            9 => {
                if v_isShared_1750_ == 0 {
                    v___x_1752_ = v___x_1749_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1755_: *mut LeanObject = *_args.add(0);
    let mut v___x_1756_: *mut LeanObject = *_args.add(1);
    let mut v___x_1757_: *mut LeanObject = *_args.add(2);
    let mut v___x_1758_: *mut LeanObject = *_args.add(3);
    let mut v_snd_1759_: *mut LeanObject = *_args.add(4);
    let mut v_fst_1760_: *mut LeanObject = *_args.add(5);
    let mut v___x_1761_: *mut LeanObject = *_args.add(6);
    let mut v___x_1762_: *mut LeanObject = *_args.add(7);
    let mut v_a_1763_: *mut LeanObject = *_args.add(8);
    let mut v___y_1764_: *mut LeanObject = *_args.add(9);
    let mut v___y_1765_: *mut LeanObject = *_args.add(10);
    let mut v___y_1766_: *mut LeanObject = *_args.add(11);
    let mut v___y_1767_: *mut LeanObject = *_args.add(12);
    let mut v___y_1768_: *mut LeanObject = *_args.add(13);
    let mut v___y_1769_: *mut LeanObject = *_args.add(14);
    let mut v___y_1770_: *mut LeanObject = *_args.add(15);
    let mut v___y_1771_: *mut LeanObject = *_args.add(16);
    let mut v___y_1772_: *mut LeanObject = *_args.add(17);
    let mut v___x_6736__boxed_1773_: usize = 0;
    let mut v___x_6737__boxed_1774_: u8 = 0;
    let mut v___x_6738__boxed_1775_: u8 = 0;
    let mut v_res_1776_: *mut LeanObject = core::ptr::null_mut();
    v___x_6736__boxed_1773_ = lean_unbox_usize(v___x_1756_);
    lean_dec(v___x_1756_);
    v___x_6737__boxed_1774_ = (lean_unbox(v___x_1757_) as u8);
    v___x_6738__boxed_1775_ = (lean_unbox(v___x_1758_) as u8);
    v_res_1776_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3(
        v___x_1755_,
        v___x_6736__boxed_1773_,
        v___x_6737__boxed_1774_,
        v___x_6738__boxed_1775_,
        v_snd_1759_,
        v_fst_1760_,
        v___x_1761_,
        v___x_1762_,
        v_a_1763_,
        v___y_1764_,
        v___y_1765_,
        v___y_1766_,
        v___y_1767_,
        v___y_1768_,
        v___y_1769_,
        v___y_1770_,
        v___y_1771_,
    );
    lean_dec(v___y_1771_);
    lean_dec_ref(v___y_1770_);
    lean_dec(v___y_1769_);
    lean_dec_ref(v___y_1768_);
    lean_dec(v___y_1767_);
    lean_dec_ref(v___y_1766_);
    lean_dec(v___y_1765_);
    lean_dec_ref(v___y_1764_);
    lean_dec_ref(v_a_1763_);
    lean_dec(v___x_1761_);
    return v_res_1776_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(
    mut v_sz_1777_: usize,
    mut v_i_1778_: usize,
    mut v_bs_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1780_: u8 = 0;
    let mut v_v_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: usize = 0;
    let mut v___x_1786_: usize = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1780_ = lean_usize_dec_lt(v_i_1778_, v_sz_1777_);
                if v___x_1780_ == 0 {
                    return v_bs_1779_;
                } else {
                    v_v_1781_ = lean_array_uget(v_bs_1779_, v_i_1778_);
                    v___x_1782_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1783_ = lean_array_uset(v_bs_1779_, v_i_1778_, v___x_1782_);
                    v___x_1784_ = l_Lean_Elab_Tactic_getNameOfIdent_x27(v_v_1781_);
                    lean_dec(v_v_1781_);
                    v___x_1785_ = 1usize;
                    v___x_1786_ = lean_usize_add(v_i_1778_, v___x_1785_);
                    v___x_1787_ = lean_array_uset(v_bs_x27_1783_, v_i_1778_, v___x_1784_);
                    v_i_1778_ = v___x_1786_;
                    v_bs_1779_ = v___x_1787_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1___boxed(
    mut v_sz_1789_: *mut LeanObject,
    mut v_i_1790_: *mut LeanObject,
    mut v_bs_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1792_: usize = 0;
    let mut v_i_boxed_1793_: usize = 0;
    let mut v_res_1794_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1792_ = lean_unbox_usize(v_sz_1789_);
    lean_dec(v_sz_1789_);
    v_i_boxed_1793_ = lean_unbox_usize(v_i_1790_);
    lean_dec(v_i_1790_);
    v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_boxed_1792_, v_i_boxed_1793_, v_bs_1791_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets(
    mut v_x_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_a_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
    mut v_a_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
    mut v_a_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1843_: usize = 0;
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: usize = 0;
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1858_: u8 = 0;
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1862_: u8 = 0;
    let mut v_a_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_a_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1878_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1824_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5;
                lean_inc(v_x_1814_);
                v___x_1825_ = l_Lean_Syntax_isOfKind(v_x_1814_, v___x_1824_);
                if v___x_1825_ == 0 {
                    lean_dec(v_x_1814_);
                    v___x_1826_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                    return v___x_1826_;
                } else {
                    v___x_1827_ = lean_unsigned_to_nat(1);
                    v___x_1828_ = l_Lean_Syntax_getArg(v_x_1814_, v___x_1827_);
                    v___x_1829_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7;
                    lean_inc(v___x_1828_);
                    v___x_1830_ = l_Lean_Syntax_isOfKind(v___x_1828_, v___x_1829_);
                    if v___x_1830_ == 0 {
                        lean_dec(v___x_1828_);
                        lean_dec(v_x_1814_);
                        v___x_1831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                        return v___x_1831_;
                    } else {
                        v___x_1832_ = 0;
                        v___x_1833_ = lean_alloc_ctor(0, 0, (11) as u32);
                        lean_ctor_set_uint8(v___x_1833_, 0 as u32, v___x_1832_);
                        lean_ctor_set_uint8(v___x_1833_, 1 as u32, v___x_1830_);
                        lean_ctor_set_uint8(v___x_1833_, 2 as u32, v___x_1832_);
                        lean_ctor_set_uint8(v___x_1833_, 3 as u32, v___x_1830_);
                        lean_ctor_set_uint8(v___x_1833_, 4 as u32, v___x_1830_);
                        lean_ctor_set_uint8(v___x_1833_, 5 as u32, v___x_1832_);
                        lean_ctor_set_uint8(v___x_1833_, 6 as u32, v___x_1830_);
                        lean_ctor_set_uint8(v___x_1833_, 7 as u32, v___x_1830_);
                        lean_ctor_set_uint8(v___x_1833_, 8 as u32, v___x_1832_);
                        lean_ctor_set_uint8(v___x_1833_, 9 as u32, v___x_1832_);
                        lean_ctor_set_uint8(v___x_1833_, 10 as u32, v___x_1832_);
                        v___x_1834_ = l_Lean_Elab_Tactic_elabExtractLetsConfig___redArg(
                            v___x_1828_,
                            v___x_1833_,
                            v___x_1830_,
                            v_a_1815_,
                            v_a_1821_,
                            v_a_1822_,
                        );
                        if lean_obj_tag(v___x_1834_) == 0 {
                            v_a_1835_ = lean_ctor_get(v___x_1834_, 0);
                            lean_inc(v_a_1835_);
                            lean_dec_ref_known(v___x_1834_, 1);
                            v___x_1836_ = l_Lean_Elab_Tactic_Conv_getLhsRhs___redArg(
                                v_a_1816_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_,
                            );
                            if lean_obj_tag(v___x_1836_) == 0 {
                                v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
                                lean_inc(v_a_1837_);
                                lean_dec_ref_known(v___x_1836_, 1);
                                v_fst_1838_ = lean_ctor_get(v_a_1837_, 0);
                                lean_inc(v_fst_1838_);
                                v_snd_1839_ = lean_ctor_get(v_a_1837_, 1);
                                lean_inc(v_snd_1839_);
                                lean_dec(v_a_1837_);
                                v___x_1840_ = lean_unsigned_to_nat(2);
                                v___x_1841_ = l_Lean_Syntax_getArg(v_x_1814_, v___x_1840_);
                                lean_dec(v_x_1814_);
                                v_ids_1842_ = l_Lean_Syntax_getArgs(v___x_1841_);
                                lean_dec(v___x_1841_);
                                v_sz_1843_ = lean_array_size(v_ids_1842_);
                                v___x_1844_ = lean_unsigned_to_nat(0);
                                v___x_1845_ = 0usize;
                                lean_inc_ref(v_ids_1842_);
                                v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__1(v_sz_1843_, v___x_1845_, v_ids_1842_);
                                v___x_1847_ = lean_array_to_list(v___x_1846_);
                                v___x_1848_ =
                                    l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed__const__1;
                                v___x_1849_ = lean_box((v___x_1832_) as usize);
                                v___x_1850_ = lean_box((v___x_1830_) as usize);
                                v___f_1851_ = lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__3___boxed
                                        as *mut core::ffi::c_void,
                                    18,
                                    9,
                                );
                                lean_closure_set(v___f_1851_, 0, v___x_1844_);
                                lean_closure_set(v___f_1851_, 1, v___x_1848_);
                                lean_closure_set(v___f_1851_, 2, v___x_1849_);
                                lean_closure_set(v___f_1851_, 3, v___x_1850_);
                                lean_closure_set(v___f_1851_, 4, v_snd_1839_);
                                lean_closure_set(v___f_1851_, 5, v_fst_1838_);
                                lean_closure_set(v___f_1851_, 6, v___x_1827_);
                                lean_closure_set(v___f_1851_, 7, v___x_1847_);
                                lean_closure_set(v___f_1851_, 8, v_a_1835_);
                                v___x_1852_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                                    v___f_1851_,
                                    v_a_1815_,
                                    v_a_1816_,
                                    v_a_1817_,
                                    v_a_1818_,
                                    v_a_1819_,
                                    v_a_1820_,
                                    v_a_1821_,
                                    v_a_1822_,
                                );
                                if lean_obj_tag(v___x_1852_) == 0 {
                                    v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
                                    lean_inc(v_a_1853_);
                                    lean_dec_ref_known(v___x_1852_, 1);
                                    v___x_1854_ = l_Lean_Elab_Tactic_extractLetsAddVarInfo(
                                        v_ids_1842_,
                                        v_a_1853_,
                                        v_a_1815_,
                                        v_a_1816_,
                                        v_a_1817_,
                                        v_a_1818_,
                                        v_a_1819_,
                                        v_a_1820_,
                                        v_a_1821_,
                                        v_a_1822_,
                                    );
                                    return v___x_1854_;
                                } else {
                                    lean_dec_ref(v_ids_1842_);
                                    v_a_1855_ = lean_ctor_get(v___x_1852_, 0);
                                    v_isSharedCheck_1862_ = (!lean_is_exclusive(v___x_1852_)) as u8;
                                    if v_isSharedCheck_1862_ == 0 {
                                        v___x_1857_ = v___x_1852_;
                                        v_isShared_1858_ = v_isSharedCheck_1862_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1855_);
                                        lean_dec(v___x_1852_);
                                        v___x_1857_ = lean_box(0);
                                        v_isShared_1858_ = v_isSharedCheck_1862_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_1835_);
                                lean_dec(v_x_1814_);
                                v_a_1863_ = lean_ctor_get(v___x_1836_, 0);
                                v_isSharedCheck_1870_ = (!lean_is_exclusive(v___x_1836_)) as u8;
                                if v_isSharedCheck_1870_ == 0 {
                                    v___x_1865_ = v___x_1836_;
                                    v_isShared_1866_ = v_isSharedCheck_1870_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1863_);
                                    lean_dec(v___x_1836_);
                                    v___x_1865_ = lean_box(0);
                                    v_isShared_1866_ = v_isSharedCheck_1870_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_x_1814_);
                            v_a_1871_ = lean_ctor_get(v___x_1834_, 0);
                            v_isSharedCheck_1878_ = (!lean_is_exclusive(v___x_1834_)) as u8;
                            if v_isSharedCheck_1878_ == 0 {
                                v___x_1873_ = v___x_1834_;
                                v_isShared_1874_ = v_isSharedCheck_1878_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_1871_);
                                lean_dec(v___x_1834_);
                                v___x_1873_ = lean_box(0);
                                v_isShared_1874_ = v_isSharedCheck_1878_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1858_ == 0 {
                    v___x_1860_ = v___x_1857_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
                    v___x_1860_ = v_reuseFailAlloc_1861_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1860_;
            }
            3 => {
                if v_isShared_1866_ == 0 {
                    v___x_1868_ = v___x_1865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
                    v___x_1868_ = v_reuseFailAlloc_1869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1868_;
            }
            5 => {
                if v_isShared_1874_ == 0 {
                    v___x_1876_ = v___x_1873_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
                    v___x_1876_ = v_reuseFailAlloc_1877_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1876_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed(
    mut v_x_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
    mut v_a_1884_: *mut LeanObject,
    mut v_a_1885_: *mut LeanObject,
    mut v_a_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1889_: *mut LeanObject = core::ptr::null_mut();
    v_res_1889_ = l_Lean_Elab_Tactic_Conv_evalExtractLets(
        v_x_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_,
        v_a_1887_,
    );
    lean_dec(v_a_1887_);
    lean_dec_ref(v_a_1886_);
    lean_dec(v_a_1885_);
    lean_dec_ref(v_a_1884_);
    lean_dec(v_a_1883_);
    lean_dec_ref(v_a_1882_);
    lean_dec(v_a_1881_);
    lean_dec_ref(v_a_1880_);
    return v_res_1889_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(
    mut v_mvarId_1890_: *mut LeanObject,
    mut v_val_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1897_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___redArg(
            v_mvarId_1890_,
            v_val_1891_,
            v___y_1893_,
        );
    return v___x_1897_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3___boxed(
    mut v_mvarId_1898_: *mut LeanObject,
    mut v_val_1899_: *mut LeanObject,
    mut v___y_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
    mut v___y_1903_: *mut LeanObject,
    mut v___y_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1905_: *mut LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3(
        v_mvarId_1898_,
        v_val_1899_,
        v___y_1900_,
        v___y_1901_,
        v___y_1902_,
        v___y_1903_,
    );
    lean_dec(v___y_1903_);
    lean_dec_ref(v___y_1902_);
    lean_dec(v___y_1901_);
    lean_dec_ref(v___y_1900_);
    return v_res_1905_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3(
    mut v_00_u03b2_1906_: *mut LeanObject,
    mut v_x_1907_: *mut LeanObject,
    mut v_x_1908_: *mut LeanObject,
    mut v_x_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___x_1910_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3___redArg(v_x_1907_, v_x_1908_, v_x_1909_);
    return v___x_1910_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(
    mut v_00_u03b2_1911_: *mut LeanObject,
    mut v_x_1912_: *mut LeanObject,
    mut v_x_1913_: usize,
    mut v_x_1914_: usize,
    mut v_x_1915_: *mut LeanObject,
    mut v_x_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___redArg(v_x_1912_, v_x_1913_, v_x_1914_, v_x_1915_, v_x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6___boxed(
    mut v_00_u03b2_1918_: *mut LeanObject,
    mut v_x_1919_: *mut LeanObject,
    mut v_x_1920_: *mut LeanObject,
    mut v_x_1921_: *mut LeanObject,
    mut v_x_1922_: *mut LeanObject,
    mut v_x_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7111__boxed_1924_: usize = 0;
    let mut v_x_7112__boxed_1925_: usize = 0;
    let mut v_res_1926_: *mut LeanObject = core::ptr::null_mut();
    v_x_7111__boxed_1924_ = lean_unbox_usize(v_x_1920_);
    lean_dec(v_x_1920_);
    v_x_7112__boxed_1925_ = lean_unbox_usize(v_x_1921_);
    lean_dec(v_x_1921_);
    v_res_1926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6(v_00_u03b2_1918_, v_x_1919_, v_x_7111__boxed_1924_, v_x_7112__boxed_1925_, v_x_1922_, v_x_1923_);
    return v_res_1926_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7(
    mut v_00_u03b2_1927_: *mut LeanObject,
    mut v_n_1928_: *mut LeanObject,
    mut v_k_1929_: *mut LeanObject,
    mut v_v_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7___redArg(v_n_1928_, v_k_1929_, v_v_1930_);
    return v___x_1931_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(
    mut v_00_u03b2_1932_: *mut LeanObject,
    mut v_depth_1933_: usize,
    mut v_keys_1934_: *mut LeanObject,
    mut v_vals_1935_: *mut LeanObject,
    mut v_heq_1936_: *mut LeanObject,
    mut v_i_1937_: *mut LeanObject,
    mut v_entries_1938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    v___x_1939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___redArg(v_depth_1933_, v_keys_1934_, v_vals_1935_, v_i_1937_, v_entries_1938_);
    return v___x_1939_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8___boxed(
    mut v_00_u03b2_1940_: *mut LeanObject,
    mut v_depth_1941_: *mut LeanObject,
    mut v_keys_1942_: *mut LeanObject,
    mut v_vals_1943_: *mut LeanObject,
    mut v_heq_1944_: *mut LeanObject,
    mut v_i_1945_: *mut LeanObject,
    mut v_entries_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1947_: usize = 0;
    let mut v_res_1948_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1947_ = lean_unbox_usize(v_depth_1941_);
    lean_dec(v_depth_1941_);
    v_res_1948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__8(v_00_u03b2_1940_, v_depth_boxed_1947_, v_keys_1942_, v_vals_1943_, v_heq_1944_, v_i_1945_, v_entries_1946_);
    lean_dec_ref(v_vals_1943_);
    lean_dec_ref(v_keys_1942_);
    return v_res_1948_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8(
    mut v_00_u03b2_1949_: *mut LeanObject,
    mut v_x_1950_: *mut LeanObject,
    mut v_x_1951_: *mut LeanObject,
    mut v_x_1952_: *mut LeanObject,
    mut v_x_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    v___x_1954_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__3_spec__3_spec__6_spec__7_spec__8___redArg(v_x_1950_, v_x_1951_, v_x_1952_, v_x_1953_);
    return v___x_1954_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1()
-> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1965_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__5;
    v___x_1966_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___closed__2;
    v___x_1967_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalExtractLets___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1968_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1964_,
        v___x_1965_,
        v___x_1966_,
        v___x_1967_,
    );
    return v___x_1968_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1___boxed(
    mut v_a_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1970_: *mut LeanObject = core::ptr::null_mut();
    v_res_1970_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
    return v_res_1970_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(
    mut v_a_1974_: *mut LeanObject,
    mut v___y_1975_: *mut LeanObject,
    mut v___y_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v___y_1978_: *mut LeanObject,
    mut v___y_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_a_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2007_: u8 = 0;
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_a_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1984_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_1976_,
                    v___y_1979_,
                    v___y_1980_,
                    v___y_1981_,
                    v___y_1982_,
                );
                if lean_obj_tag(v___x_1984_) == 0 {
                    v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
                    lean_inc_n(v_a_1985_, 2);
                    lean_dec_ref_known(v___x_1984_, 1);
                    v___x_1986_ = l_Lean_Meta_liftLets(
                        v_a_1985_,
                        v_a_1974_,
                        v___y_1979_,
                        v___y_1980_,
                        v___y_1981_,
                        v___y_1982_,
                    );
                    if lean_obj_tag(v___x_1986_) == 0 {
                        v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
                        lean_inc(v_a_1987_);
                        lean_dec_ref_known(v___x_1986_, 1);
                        v___x_1988_ = lean_expr_eqv(v_a_1985_, v_a_1987_);
                        lean_dec(v_a_1985_);
                        if v___x_1988_ == 0 {
                            v___x_1989_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_a_1987_,
                                v___y_1975_,
                                v___y_1976_,
                                v___y_1977_,
                                v___y_1978_,
                                v___y_1979_,
                                v___y_1980_,
                                v___y_1981_,
                                v___y_1982_,
                            );
                            return v___x_1989_;
                        } else {
                            v___x_1990_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v___y_1976_,
                                v___y_1979_,
                                v___y_1980_,
                                v___y_1981_,
                                v___y_1982_,
                            );
                            if lean_obj_tag(v___x_1990_) == 0 {
                                v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
                                lean_inc(v_a_1991_);
                                lean_dec_ref_known(v___x_1990_, 1);
                                v___x_1992_ =
                                    l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___closed__1;
                                v___x_1993_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once), _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
                                v___x_1994_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_1992_,
                                    v_a_1991_,
                                    v___x_1993_,
                                    v___y_1979_,
                                    v___y_1980_,
                                    v___y_1981_,
                                    v___y_1982_,
                                );
                                if lean_obj_tag(v___x_1994_) == 0 {
                                    lean_dec_ref_known(v___x_1994_, 1);
                                    v___x_1995_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                        v_a_1987_,
                                        v___y_1975_,
                                        v___y_1976_,
                                        v___y_1977_,
                                        v___y_1978_,
                                        v___y_1979_,
                                        v___y_1980_,
                                        v___y_1981_,
                                        v___y_1982_,
                                    );
                                    return v___x_1995_;
                                } else {
                                    lean_dec(v_a_1987_);
                                    return v___x_1994_;
                                }
                            } else {
                                lean_dec(v_a_1987_);
                                v_a_1996_ = lean_ctor_get(v___x_1990_, 0);
                                v_isSharedCheck_2003_ = (!lean_is_exclusive(v___x_1990_)) as u8;
                                if v_isSharedCheck_2003_ == 0 {
                                    v___x_1998_ = v___x_1990_;
                                    v_isShared_1999_ = v_isSharedCheck_2003_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1996_);
                                    lean_dec(v___x_1990_);
                                    v___x_1998_ = lean_box(0);
                                    v_isShared_1999_ = v_isSharedCheck_2003_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_1985_);
                        v_a_2004_ = lean_ctor_get(v___x_1986_, 0);
                        v_isSharedCheck_2011_ = (!lean_is_exclusive(v___x_1986_)) as u8;
                        if v_isSharedCheck_2011_ == 0 {
                            v___x_2006_ = v___x_1986_;
                            v_isShared_2007_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2004_);
                            lean_dec(v___x_1986_);
                            v___x_2006_ = lean_box(0);
                            v_isShared_2007_ = v_isSharedCheck_2011_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_1974_);
                    v_a_2012_ = lean_ctor_get(v___x_1984_, 0);
                    v_isSharedCheck_2019_ = (!lean_is_exclusive(v___x_1984_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_2014_ = v___x_1984_;
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2012_);
                        lean_dec(v___x_1984_);
                        v___x_2014_ = lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1999_ == 0 {
                    v___x_2001_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2001_;
            }
            3 => {
                if v_isShared_2007_ == 0 {
                    v___x_2009_ = v___x_2006_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2009_;
            }
            5 => {
                if v_isShared_2015_ == 0 {
                    v___x_2017_ = v___x_2014_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2018_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed(
    mut v_a_2020_: *mut LeanObject,
    mut v___y_2021_: *mut LeanObject,
    mut v___y_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
    mut v___y_2025_: *mut LeanObject,
    mut v___y_2026_: *mut LeanObject,
    mut v___y_2027_: *mut LeanObject,
    mut v___y_2028_: *mut LeanObject,
    mut v___y_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2030_: *mut LeanObject = core::ptr::null_mut();
    v_res_2030_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0(
        v_a_2020_,
        v___y_2021_,
        v___y_2022_,
        v___y_2023_,
        v___y_2024_,
        v___y_2025_,
        v___y_2026_,
        v___y_2027_,
        v___y_2028_,
    );
    lean_dec(v___y_2028_);
    lean_dec_ref(v___y_2027_);
    lean_dec(v___y_2026_);
    lean_dec_ref(v___y_2025_);
    lean_dec(v___y_2024_);
    lean_dec_ref(v___y_2023_);
    lean_dec(v___y_2022_);
    lean_dec_ref(v___y_2021_);
    return v_res_2030_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets(
    mut v_x_2038_: *mut LeanObject,
    mut v_a_2039_: *mut LeanObject,
    mut v_a_2040_: *mut LeanObject,
    mut v_a_2041_: *mut LeanObject,
    mut v_a_2042_: *mut LeanObject,
    mut v_a_2043_: *mut LeanObject,
    mut v_a_2044_: *mut LeanObject,
    mut v_a_2045_: *mut LeanObject,
    mut v_a_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: u8 = 0;
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: u8 = 0;
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2065_: u8 = 0;
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2069_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2048_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1;
                lean_inc(v_x_2038_);
                v___x_2049_ = l_Lean_Syntax_isOfKind(v_x_2038_, v___x_2048_);
                if v___x_2049_ == 0 {
                    lean_dec(v_x_2038_);
                    v___x_2050_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                    return v___x_2050_;
                } else {
                    v___x_2051_ = lean_unsigned_to_nat(1);
                    v___x_2052_ = l_Lean_Syntax_getArg(v_x_2038_, v___x_2051_);
                    lean_dec(v_x_2038_);
                    v___x_2053_ = l_Lean_Elab_Tactic_Conv_evalExtractLets___closed__7;
                    lean_inc(v___x_2052_);
                    v___x_2054_ = l_Lean_Syntax_isOfKind(v___x_2052_, v___x_2053_);
                    if v___x_2054_ == 0 {
                        lean_dec(v___x_2052_);
                        v___x_2055_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
                        return v___x_2055_;
                    } else {
                        v___x_2056_ = 0;
                        v___x_2057_ = lean_alloc_ctor(0, 0, (11) as u32);
                        lean_ctor_set_uint8(v___x_2057_, 0 as u32, v___x_2056_);
                        lean_ctor_set_uint8(v___x_2057_, 1 as u32, v___x_2054_);
                        lean_ctor_set_uint8(v___x_2057_, 2 as u32, v___x_2056_);
                        lean_ctor_set_uint8(v___x_2057_, 3 as u32, v___x_2054_);
                        lean_ctor_set_uint8(v___x_2057_, 4 as u32, v___x_2054_);
                        lean_ctor_set_uint8(v___x_2057_, 5 as u32, v___x_2056_);
                        lean_ctor_set_uint8(v___x_2057_, 6 as u32, v___x_2054_);
                        lean_ctor_set_uint8(v___x_2057_, 7 as u32, v___x_2054_);
                        lean_ctor_set_uint8(v___x_2057_, 8 as u32, v___x_2056_);
                        lean_ctor_set_uint8(v___x_2057_, 9 as u32, v___x_2054_);
                        lean_ctor_set_uint8(v___x_2057_, 10 as u32, v___x_2054_);
                        v___x_2058_ = l_Lean_Elab_Tactic_elabLiftLetsConfig___redArg(
                            v___x_2052_,
                            v___x_2057_,
                            v___x_2054_,
                            v_a_2039_,
                            v_a_2045_,
                            v_a_2046_,
                        );
                        if lean_obj_tag(v___x_2058_) == 0 {
                            v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
                            lean_inc(v_a_2059_);
                            lean_dec_ref_known(v___x_2058_, 1);
                            v___f_2060_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_Conv_evalLiftLets___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            lean_closure_set(v___f_2060_, 0, v_a_2059_);
                            v___x_2061_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                                v___f_2060_,
                                v_a_2039_,
                                v_a_2040_,
                                v_a_2041_,
                                v_a_2042_,
                                v_a_2043_,
                                v_a_2044_,
                                v_a_2045_,
                                v_a_2046_,
                            );
                            return v___x_2061_;
                        } else {
                            v_a_2062_ = lean_ctor_get(v___x_2058_, 0);
                            v_isSharedCheck_2069_ = (!lean_is_exclusive(v___x_2058_)) as u8;
                            if v_isSharedCheck_2069_ == 0 {
                                v___x_2064_ = v___x_2058_;
                                v_isShared_2065_ = v_isSharedCheck_2069_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2062_);
                                lean_dec(v___x_2058_);
                                v___x_2064_ = lean_box(0);
                                v_isShared_2065_ = v_isSharedCheck_2069_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2065_ == 0 {
                    v___x_2067_ = v___x_2064_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2062_);
                    v___x_2067_ = v_reuseFailAlloc_2068_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2067_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed(
    mut v_x_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
    mut v_a_2073_: *mut LeanObject,
    mut v_a_2074_: *mut LeanObject,
    mut v_a_2075_: *mut LeanObject,
    mut v_a_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2080_: *mut LeanObject = core::ptr::null_mut();
    v_res_2080_ = l_Lean_Elab_Tactic_Conv_evalLiftLets(
        v_x_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_,
        v_a_2078_,
    );
    lean_dec(v_a_2078_);
    lean_dec_ref(v_a_2077_);
    lean_dec(v_a_2076_);
    lean_dec_ref(v_a_2075_);
    lean_dec(v_a_2074_);
    lean_dec_ref(v_a_2073_);
    lean_dec(v_a_2072_);
    lean_dec_ref(v_a_2071_);
    return v_res_2080_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1()
-> *mut LeanObject {
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    v___x_2089_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2090_ = l_Lean_Elab_Tactic_Conv_evalLiftLets___closed__1;
    v___x_2091_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___closed__1;
    v___x_2092_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalLiftLets___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2093_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2089_,
        v___x_2090_,
        v___x_2091_,
        v___x_2092_,
    );
    return v___x_2093_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1___boxed(
    mut v_a_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2095_: *mut LeanObject = core::ptr::null_mut();
    v_res_2095_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
    return v_res_2095_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(
    mut v___y_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2127_: u8 = 0;
    let mut v_a_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2131_: u8 = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_a_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2139_: u8 = 0;
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2108_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                    v___y_2100_,
                    v___y_2103_,
                    v___y_2104_,
                    v___y_2105_,
                    v___y_2106_,
                );
                if lean_obj_tag(v___x_2108_) == 0 {
                    v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
                    lean_inc_n(v_a_2109_, 2);
                    lean_dec_ref_known(v___x_2108_, 1);
                    v___x_2110_ = l_Lean_Meta_letToHave(
                        v_a_2109_,
                        v___y_2103_,
                        v___y_2104_,
                        v___y_2105_,
                        v___y_2106_,
                    );
                    if lean_obj_tag(v___x_2110_) == 0 {
                        v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
                        lean_inc(v_a_2111_);
                        lean_dec_ref_known(v___x_2110_, 1);
                        v___x_2112_ = lean_expr_eqv(v_a_2109_, v_a_2111_);
                        lean_dec(v_a_2109_);
                        if v___x_2112_ == 0 {
                            v___x_2113_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                v_a_2111_,
                                v___y_2099_,
                                v___y_2100_,
                                v___y_2101_,
                                v___y_2102_,
                                v___y_2103_,
                                v___y_2104_,
                                v___y_2105_,
                                v___y_2106_,
                            );
                            return v___x_2113_;
                        } else {
                            v___x_2114_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                                v___y_2100_,
                                v___y_2103_,
                                v___y_2104_,
                                v___y_2105_,
                                v___y_2106_,
                            );
                            if lean_obj_tag(v___x_2114_) == 0 {
                                v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
                                lean_inc(v_a_2115_);
                                lean_dec_ref_known(v___x_2114_, 1);
                                v___x_2116_ =
                                    l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___closed__1;
                                v___x_2117_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2_once), _init_l_Lean_Elab_Tactic_Conv_evalExtractLets___lam__2___closed__2);
                                v___x_2118_ = l_Lean_Meta_throwTacticEx___redArg(
                                    v___x_2116_,
                                    v_a_2115_,
                                    v___x_2117_,
                                    v___y_2103_,
                                    v___y_2104_,
                                    v___y_2105_,
                                    v___y_2106_,
                                );
                                if lean_obj_tag(v___x_2118_) == 0 {
                                    lean_dec_ref_known(v___x_2118_, 1);
                                    v___x_2119_ = l_Lean_Elab_Tactic_Conv_changeLhs(
                                        v_a_2111_,
                                        v___y_2099_,
                                        v___y_2100_,
                                        v___y_2101_,
                                        v___y_2102_,
                                        v___y_2103_,
                                        v___y_2104_,
                                        v___y_2105_,
                                        v___y_2106_,
                                    );
                                    return v___x_2119_;
                                } else {
                                    lean_dec(v_a_2111_);
                                    return v___x_2118_;
                                }
                            } else {
                                lean_dec(v_a_2111_);
                                v_a_2120_ = lean_ctor_get(v___x_2114_, 0);
                                v_isSharedCheck_2127_ = (!lean_is_exclusive(v___x_2114_)) as u8;
                                if v_isSharedCheck_2127_ == 0 {
                                    v___x_2122_ = v___x_2114_;
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2120_);
                                    lean_dec(v___x_2114_);
                                    v___x_2122_ = lean_box(0);
                                    v_isShared_2123_ = v_isSharedCheck_2127_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_2109_);
                        v_a_2128_ = lean_ctor_get(v___x_2110_, 0);
                        v_isSharedCheck_2135_ = (!lean_is_exclusive(v___x_2110_)) as u8;
                        if v_isSharedCheck_2135_ == 0 {
                            v___x_2130_ = v___x_2110_;
                            v_isShared_2131_ = v_isSharedCheck_2135_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2128_);
                            lean_dec(v___x_2110_);
                            v___x_2130_ = lean_box(0);
                            v_isShared_2131_ = v_isSharedCheck_2135_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2136_ = lean_ctor_get(v___x_2108_, 0);
                    v_isSharedCheck_2143_ = (!lean_is_exclusive(v___x_2108_)) as u8;
                    if v_isSharedCheck_2143_ == 0 {
                        v___x_2138_ = v___x_2108_;
                        v_isShared_2139_ = v_isSharedCheck_2143_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2136_);
                        lean_dec(v___x_2108_);
                        v___x_2138_ = lean_box(0);
                        v_isShared_2139_ = v_isSharedCheck_2143_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2123_ == 0 {
                    v___x_2125_ = v___x_2122_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
                    v___x_2125_ = v_reuseFailAlloc_2126_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2125_;
            }
            3 => {
                if v_isShared_2131_ == 0 {
                    v___x_2133_ = v___x_2130_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
                    v___x_2133_ = v_reuseFailAlloc_2134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2133_;
            }
            5 => {
                if v_isShared_2139_ == 0 {
                    v___x_2141_ = v___x_2138_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
                    v___x_2141_ = v_reuseFailAlloc_2142_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0___boxed(
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2153_: *mut LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___lam__0(
        v___y_2144_,
        v___y_2145_,
        v___y_2146_,
        v___y_2147_,
        v___y_2148_,
        v___y_2149_,
        v___y_2150_,
        v___y_2151_,
    );
    lean_dec(v___y_2151_);
    lean_dec_ref(v___y_2150_);
    lean_dec(v___y_2149_);
    lean_dec_ref(v___y_2148_);
    lean_dec(v___y_2147_);
    lean_dec_ref(v___y_2146_);
    lean_dec(v___y_2145_);
    lean_dec_ref(v___y_2144_);
    return v_res_2153_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave(
    mut v_x_2162_: *mut LeanObject,
    mut v_a_2163_: *mut LeanObject,
    mut v_a_2164_: *mut LeanObject,
    mut v_a_2165_: *mut LeanObject,
    mut v_a_2166_: *mut LeanObject,
    mut v_a_2167_: *mut LeanObject,
    mut v_a_2168_: *mut LeanObject,
    mut v_a_2169_: *mut LeanObject,
    mut v_a_2170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: u8 = 0;
    v___x_2172_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1;
    v___x_2173_ = l_Lean_Syntax_isOfKind(v_x_2162_, v___x_2172_);
    if v___x_2173_ == 0 {
        let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
        v___x_2174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalExtractLets_spec__0___redArg();
        return v___x_2174_;
    } else {
        let mut v___f_2175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
        v___f_2175_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__2;
        v___x_2176_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_2175_,
            v_a_2163_,
            v_a_2164_,
            v_a_2165_,
            v_a_2166_,
            v_a_2167_,
            v_a_2168_,
            v_a_2169_,
            v_a_2170_,
        );
        return v___x_2176_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed(
    mut v_x_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
    mut v_a_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
    mut v_a_2184_: *mut LeanObject,
    mut v_a_2185_: *mut LeanObject,
    mut v_a_2186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2187_: *mut LeanObject = core::ptr::null_mut();
    v_res_2187_ = l_Lean_Elab_Tactic_Conv_evalLetToHave(
        v_x_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_,
        v_a_2185_,
    );
    lean_dec(v_a_2185_);
    lean_dec_ref(v_a_2184_);
    lean_dec(v_a_2183_);
    lean_dec_ref(v_a_2182_);
    lean_dec(v_a_2181_);
    lean_dec_ref(v_a_2180_);
    lean_dec(v_a_2179_);
    lean_dec_ref(v_a_2178_);
    return v_res_2187_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1()
-> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    v___x_2196_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2197_ = l_Lean_Elab_Tactic_Conv_evalLetToHave___closed__1;
    v___x_2198_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___closed__1;
    v___x_2199_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalLetToHave___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2200_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2196_,
        v___x_2197_,
        v___x_2198_,
        v___x_2199_,
    );
    return v___x_2200_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1___boxed(
    mut v_a_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2202_: *mut LeanObject = core::ptr::null_mut();
    v_res_2202_ = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
    return v_res_2202_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Lets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalExtractLets___regBuiltin_Lean_Elab_Tactic_Conv_evalExtractLets__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLiftLets___regBuiltin_Lean_Elab_Tactic_Conv_evalLiftLets__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Lets_0__Lean_Elab_Tactic_Conv_evalLetToHave___regBuiltin_Lean_Elab_Tactic_Conv_evalLetToHave__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Lets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Lets(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Lets(builtin);
}
