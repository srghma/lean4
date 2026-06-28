// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Have
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Basic Lean.Elab.Tactic.Do.ProofMode.Focus Lean.Elab.Tactic.ElabTerm
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr6,
    l_Lean_Name_num___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getId, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd, l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21,
    l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo, l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_elabTerm,
    l_Lean_Elab_Tactic_elabTermEnsuringType, runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_consumeMData, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp7, l_Lean_mkApp8,
    l_Lean_mkApp10, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, runtime_initialize_Std_Tactic_Do_Syntax,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9,
    lean_apply_10, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value: LeanStringObject<
    4,
> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value: LeanStringObject<
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value: LeanStringObject<
    6,
> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [72, 97, 118, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [100, 117, 112, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5_value: LeanStringObject<
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
    m_data: [72, 121, 112, 111, 116, 104, 101, 115, 105, 115, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7_value: LeanStringObject<
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
    m_data: [32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value: LeanStringObject<5> =
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
        m_data: [109, 100, 117, 112, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__3_value)
                as *mut LeanObject,
            8619307128568967249 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value: LeanStringObject<6> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__5_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 77, 68, 117, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__2_value) as *mut LeanObject,16089473174266965463 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [104, 97, 118, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value: LeanStringObject<6> =
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
        m_data: [109, 104, 97, 118, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__0_value)
                as *mut LeanObject,
            4297332248507658187 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 77, 72, 97, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__0_value) as *mut LeanObject,16508224334496205735 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 112, 108, 97, 99, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value: LeanStringObject<9> =
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
        m_data: [109, 114, 101, 112, 108, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__0_value)
                as *mut LeanObject,
            6001227252242998451 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 77, 82, 101, 112, 108, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__1_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__0_value) as *mut LeanObject,4360817995873788650 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    v___x_1232_ = lean_box(0);
    v___x_1233_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1234_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1234_, 0, v___x_1233_);
    lean_ctor_set(v___x_1234_, 1, v___x_1232_);
    return v___x_1234_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    v___x_1236_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___closed__0);
    v___x_1237_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1237_, 0, v___x_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg___boxed(
    mut v___y_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1239_: *mut LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
    return v_res_1239_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(
    mut v_00_u03b1_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    v___x_1250_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
    return v___x_1250_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___boxed(
    mut v_00_u03b1_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1261_: *mut LeanObject = core::ptr::null_mut();
    v_res_1261_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0(
            v_00_u03b1_1251_,
            v___y_1252_,
            v___y_1253_,
            v___y_1254_,
            v___y_1255_,
            v___y_1256_,
            v___y_1257_,
            v___y_1258_,
            v___y_1259_,
        );
    lean_dec(v___y_1259_);
    lean_dec_ref(v___y_1258_);
    lean_dec(v___y_1257_);
    lean_dec_ref(v___y_1256_);
    lean_dec(v___y_1255_);
    lean_dec_ref(v___y_1254_);
    lean_dec(v___y_1253_);
    lean_dec_ref(v___y_1252_);
    return v_res_1261_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(
    mut v___y_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v_r_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1294_: u8 = 0;
    let mut v_unused_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1264_ = lean_st_ref_get(v___y_1262_);
                v_ngen_1265_ = lean_ctor_get(v___x_1264_, 2);
                lean_inc_ref(v_ngen_1265_);
                lean_dec(v___x_1264_);
                v_namePrefix_1266_ = lean_ctor_get(v_ngen_1265_, 0);
                v_idx_1267_ = lean_ctor_get(v_ngen_1265_, 1);
                v_isSharedCheck_1296_ = (!lean_is_exclusive(v_ngen_1265_)) as u8;
                if v_isSharedCheck_1296_ == 0 {
                    v___x_1269_ = v_ngen_1265_;
                    v_isShared_1270_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1267_);
                    lean_inc(v_namePrefix_1266_);
                    lean_dec(v_ngen_1265_);
                    v___x_1269_ = lean_box(0);
                    v_isShared_1270_ = v_isSharedCheck_1296_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1271_ = lean_st_ref_take(v___y_1262_);
                v_env_1272_ = lean_ctor_get(v___x_1271_, 0);
                v_nextMacroScope_1273_ = lean_ctor_get(v___x_1271_, 1);
                v_auxDeclNGen_1274_ = lean_ctor_get(v___x_1271_, 3);
                v_traceState_1275_ = lean_ctor_get(v___x_1271_, 4);
                v_cache_1276_ = lean_ctor_get(v___x_1271_, 5);
                v_messages_1277_ = lean_ctor_get(v___x_1271_, 6);
                v_infoState_1278_ = lean_ctor_get(v___x_1271_, 7);
                v_snapshotTasks_1279_ = lean_ctor_get(v___x_1271_, 8);
                v_isSharedCheck_1294_ = (!lean_is_exclusive(v___x_1271_)) as u8;
                if v_isSharedCheck_1294_ == 0 {
                    v_unused_1295_ = lean_ctor_get(v___x_1271_, 2);
                    lean_dec(v_unused_1295_);
                    v___x_1281_ = v___x_1271_;
                    v_isShared_1282_ = v_isSharedCheck_1294_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1279_);
                    lean_inc(v_infoState_1278_);
                    lean_inc(v_messages_1277_);
                    lean_inc(v_cache_1276_);
                    lean_inc(v_traceState_1275_);
                    lean_inc(v_auxDeclNGen_1274_);
                    lean_inc(v_nextMacroScope_1273_);
                    lean_inc(v_env_1272_);
                    lean_dec(v___x_1271_);
                    v___x_1281_ = lean_box(0);
                    v_isShared_1282_ = v_isSharedCheck_1294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_1267_);
                lean_inc(v_namePrefix_1266_);
                v_r_1283_ = l_Lean_Name_num___override(v_namePrefix_1266_, v_idx_1267_);
                v___x_1284_ = lean_unsigned_to_nat(1);
                v___x_1285_ = lean_nat_add(v_idx_1267_, v___x_1284_);
                lean_dec(v_idx_1267_);
                if v_isShared_1270_ == 0 {
                    lean_ctor_set(v___x_1269_, 1, v___x_1285_);
                    v___x_1287_ = v___x_1269_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_namePrefix_1266_);
                    lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1285_);
                    v___x_1287_ = v_reuseFailAlloc_1293_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1282_ == 0 {
                    lean_ctor_set(v___x_1281_, 2, v___x_1287_);
                    v___x_1289_ = v___x_1281_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_env_1272_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_nextMacroScope_1273_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 2, v___x_1287_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_auxDeclNGen_1274_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_traceState_1275_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 5, v_cache_1276_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 6, v_messages_1277_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 7, v_infoState_1278_);
                    lean_ctor_set(v_reuseFailAlloc_1292_, 8, v_snapshotTasks_1279_);
                    v___x_1289_ = v_reuseFailAlloc_1292_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1290_ = lean_st_ref_set(v___y_1262_, v___x_1289_);
                v___x_1291_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1291_, 0, v_r_1283_);
                return v___x_1291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg___boxed(
    mut v___y_1297_: *mut LeanObject,
    mut v___y_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1299_: *mut LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(
        v___y_1297_,
    );
    lean_dec(v___y_1297_);
    return v_res_1299_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    v___x_1309_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(
        v___y_1307_,
    );
    return v___x_1309_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___boxed(
    mut v___y_1310_: *mut LeanObject,
    mut v___y_1311_: *mut LeanObject,
    mut v___y_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1319_: *mut LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1(
        v___y_1310_,
        v___y_1311_,
        v___y_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
    );
    lean_dec(v___y_1317_);
    lean_dec_ref(v___y_1316_);
    lean_dec(v___y_1315_);
    lean_dec_ref(v___y_1314_);
    lean_dec(v___y_1313_);
    lean_dec_ref(v___y_1312_);
    lean_dec(v___y_1311_);
    lean_dec_ref(v___y_1310_);
    return v_res_1319_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(
    mut v_x_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
    mut v___y_1322_: *mut LeanObject,
    mut v___y_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1324_);
    lean_inc_ref(v___y_1323_);
    lean_inc(v___y_1322_);
    lean_inc_ref(v___y_1321_);
    v___x_1330_ = lean_apply_9(
        v_x_1320_,
        v___y_1321_,
        v___y_1322_,
        v___y_1323_,
        v___y_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
        lean_box(0),
    );
    return v___x_1330_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed(
    mut v_x_1331_: *mut LeanObject,
    mut v___y_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
    mut v___y_1338_: *mut LeanObject,
    mut v___y_1339_: *mut LeanObject,
    mut v___y_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1341_: *mut LeanObject = core::ptr::null_mut();
    v_res_1341_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0(v_x_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
    lean_dec(v___y_1335_);
    lean_dec_ref(v___y_1334_);
    lean_dec(v___y_1333_);
    lean_dec_ref(v___y_1332_);
    return v_res_1341_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(
    mut v_mvarId_1342_: *mut LeanObject,
    mut v_x_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
    mut v___y_1346_: *mut LeanObject,
    mut v___y_1347_: *mut LeanObject,
    mut v___y_1348_: *mut LeanObject,
    mut v___y_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
    mut v___y_1351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1358_: u8 = 0;
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1347_);
                lean_inc_ref(v___y_1346_);
                lean_inc(v___y_1345_);
                lean_inc_ref(v___y_1344_);
                v___f_1353_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_1353_, 0, v_x_1343_);
                lean_closure_set(v___f_1353_, 1, v___y_1344_);
                lean_closure_set(v___f_1353_, 2, v___y_1345_);
                lean_closure_set(v___f_1353_, 3, v___y_1346_);
                lean_closure_set(v___f_1353_, 4, v___y_1347_);
                v___x_1354_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1342_,
                    v___f_1353_,
                    v___y_1348_,
                    v___y_1349_,
                    v___y_1350_,
                    v___y_1351_,
                );
                if lean_obj_tag(v___x_1354_) == 0 {
                    return v___x_1354_;
                } else {
                    v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
                    v_isSharedCheck_1362_ = (!lean_is_exclusive(v___x_1354_)) as u8;
                    if v_isSharedCheck_1362_ == 0 {
                        v___x_1357_ = v___x_1354_;
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1355_);
                        lean_dec(v___x_1354_);
                        v___x_1357_ = lean_box(0);
                        v_isShared_1358_ = v_isSharedCheck_1362_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1358_ == 0 {
                    v___x_1360_ = v___x_1357_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
                    v___x_1360_ = v_reuseFailAlloc_1361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg___boxed(
    mut v_mvarId_1363_: *mut LeanObject,
    mut v_x_1364_: *mut LeanObject,
    mut v___y_1365_: *mut LeanObject,
    mut v___y_1366_: *mut LeanObject,
    mut v___y_1367_: *mut LeanObject,
    mut v___y_1368_: *mut LeanObject,
    mut v___y_1369_: *mut LeanObject,
    mut v___y_1370_: *mut LeanObject,
    mut v___y_1371_: *mut LeanObject,
    mut v___y_1372_: *mut LeanObject,
    mut v___y_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1374_: *mut LeanObject = core::ptr::null_mut();
    v_res_1374_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(
            v_mvarId_1363_,
            v_x_1364_,
            v___y_1365_,
            v___y_1366_,
            v___y_1367_,
            v___y_1368_,
            v___y_1369_,
            v___y_1370_,
            v___y_1371_,
            v___y_1372_,
        );
    lean_dec(v___y_1372_);
    lean_dec_ref(v___y_1371_);
    lean_dec(v___y_1370_);
    lean_dec_ref(v___y_1369_);
    lean_dec(v___y_1368_);
    lean_dec_ref(v___y_1367_);
    lean_dec(v___y_1366_);
    lean_dec_ref(v___y_1365_);
    return v_res_1374_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(
    mut v_00_u03b1_1375_: *mut LeanObject,
    mut v_mvarId_1376_: *mut LeanObject,
    mut v_x_1377_: *mut LeanObject,
    mut v___y_1378_: *mut LeanObject,
    mut v___y_1379_: *mut LeanObject,
    mut v___y_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    v___x_1387_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(
            v_mvarId_1376_,
            v_x_1377_,
            v___y_1378_,
            v___y_1379_,
            v___y_1380_,
            v___y_1381_,
            v___y_1382_,
            v___y_1383_,
            v___y_1384_,
            v___y_1385_,
        );
    return v___x_1387_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___boxed(
    mut v_00_u03b1_1388_: *mut LeanObject,
    mut v_mvarId_1389_: *mut LeanObject,
    mut v_x_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
    mut v___y_1394_: *mut LeanObject,
    mut v___y_1395_: *mut LeanObject,
    mut v___y_1396_: *mut LeanObject,
    mut v___y_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1400_: *mut LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4(
        v_00_u03b1_1388_,
        v_mvarId_1389_,
        v_x_1390_,
        v___y_1391_,
        v___y_1392_,
        v___y_1393_,
        v___y_1394_,
        v___y_1395_,
        v___y_1396_,
        v___y_1397_,
        v___y_1398_,
    );
    lean_dec(v___y_1398_);
    lean_dec_ref(v___y_1397_);
    lean_dec(v___y_1396_);
    lean_dec_ref(v___y_1395_);
    lean_dec(v___y_1394_);
    lean_dec_ref(v___y_1393_);
    lean_dec(v___y_1392_);
    lean_dec_ref(v___y_1391_);
    return v_res_1400_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(
    mut v_x_1401_: *mut LeanObject,
    mut v_x_1402_: *mut LeanObject,
    mut v_x_1403_: *mut LeanObject,
    mut v_x_1404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: u8 = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1405_ = lean_ctor_get(v_x_1401_, 0);
                v_vs_1406_ = lean_ctor_get(v_x_1401_, 1);
                v_isSharedCheck_1430_ = (!lean_is_exclusive(v_x_1401_)) as u8;
                if v_isSharedCheck_1430_ == 0 {
                    v___x_1408_ = v_x_1401_;
                    v_isShared_1409_ = v_isSharedCheck_1430_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_1406_);
                    lean_inc(v_ks_1405_);
                    lean_dec(v_x_1401_);
                    v___x_1408_ = lean_box(0);
                    v_isShared_1409_ = v_isSharedCheck_1430_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1410_ = lean_array_get_size(v_ks_1405_);
                v___x_1411_ = lean_nat_dec_lt(v_x_1402_, v___x_1410_);
                if v___x_1411_ == 0 {
                    lean_dec(v_x_1402_);
                    v___x_1412_ = lean_array_push(v_ks_1405_, v_x_1403_);
                    v___x_1413_ = lean_array_push(v_vs_1406_, v_x_1404_);
                    if v_isShared_1409_ == 0 {
                        lean_ctor_set(v___x_1408_, 1, v___x_1413_);
                        lean_ctor_set(v___x_1408_, 0, v___x_1412_);
                        v___x_1415_ = v___x_1408_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1412_);
                        lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1413_);
                        v___x_1415_ = v_reuseFailAlloc_1416_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1417_ = lean_array_fget_borrowed(v_ks_1405_, v_x_1402_);
                    v___x_1418_ = l_Lean_instBEqMVarId_beq(v_x_1403_, v_k_x27_1417_);
                    if v___x_1418_ == 0 {
                        if v_isShared_1409_ == 0 {
                            v___x_1420_ = v___x_1408_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_ks_1405_);
                            lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_vs_1406_);
                            v___x_1420_ = v_reuseFailAlloc_1424_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1425_ = lean_array_fset(v_ks_1405_, v_x_1402_, v_x_1403_);
                        v___x_1426_ = lean_array_fset(v_vs_1406_, v_x_1402_, v_x_1404_);
                        lean_dec(v_x_1402_);
                        if v_isShared_1409_ == 0 {
                            lean_ctor_set(v___x_1408_, 1, v___x_1426_);
                            lean_ctor_set(v___x_1408_, 0, v___x_1425_);
                            v___x_1428_ = v___x_1408_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1429_, 0, v___x_1425_);
                            lean_ctor_set(v_reuseFailAlloc_1429_, 1, v___x_1426_);
                            v___x_1428_ = v_reuseFailAlloc_1429_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1415_;
            }
            3 => {
                v___x_1421_ = lean_unsigned_to_nat(1);
                v___x_1422_ = lean_nat_add(v_x_1402_, v___x_1421_);
                lean_dec(v_x_1402_);
                v_x_1401_ = v___x_1420_;
                v_x_1402_ = v___x_1422_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(
    mut v_n_1431_: *mut LeanObject,
    mut v_k_1432_: *mut LeanObject,
    mut v_v_1433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = lean_unsigned_to_nat(0);
    v___x_1435_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_1431_, v___x_1434_, v_k_1432_, v_v_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_1436_: usize = 0;
    let mut v___x_1437_: usize = 0;
    let mut v___x_1438_: usize = 0;
    v___x_1436_ = 5usize;
    v___x_1437_ = 1usize;
    v___x_1438_ = lean_usize_shift_left(v___x_1437_, v___x_1436_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: usize = 0;
    let mut v___x_1441_: usize = 0;
    v___x_1439_ = 1usize;
    v___x_1440_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__0);
    v___x_1441_ = lean_usize_sub(v___x_1440_, v___x_1439_);
    return v___x_1441_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_1442_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(
    mut v_x_1443_: *mut LeanObject,
    mut v_x_1444_: usize,
    mut v_x_1445_: usize,
    mut v_x_1446_: *mut LeanObject,
    mut v_x_1447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: usize = 0;
    let mut v___x_1450_: usize = 0;
    let mut v___x_1451_: usize = 0;
    let mut v___x_1452_: usize = 0;
    let mut v_j_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v_v_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1472_: u8 = 0;
    let mut v___x_1473_: u8 = 0;
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1479_: u8 = 0;
    let mut v_node_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1483_: u8 = 0;
    let mut v___x_1484_: usize = 0;
    let mut v___x_1485_: usize = 0;
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_unused_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: u8 = 0;
    let mut v_ks_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: usize = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_reuseFailAlloc_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1443_) == 0 {
                    v_es_1448_ = lean_ctor_get(v_x_1443_, 0);
                    v___x_1449_ = 5usize;
                    v___x_1450_ = 1usize;
                    v___x_1451_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__1);
                    v___x_1452_ = lean_usize_land(v_x_1444_, v___x_1451_);
                    v_j_1453_ = lean_usize_to_nat(v___x_1452_);
                    v___x_1454_ = lean_array_get_size(v_es_1448_);
                    v___x_1455_ = lean_nat_dec_lt(v_j_1453_, v___x_1454_);
                    if v___x_1455_ == 0 {
                        lean_dec(v_j_1453_);
                        lean_dec(v_x_1447_);
                        lean_dec(v_x_1446_);
                        return v_x_1443_;
                    } else {
                        lean_inc_ref(v_es_1448_);
                        v_isSharedCheck_1492_ = (!lean_is_exclusive(v_x_1443_)) as u8;
                        if v_isSharedCheck_1492_ == 0 {
                            v_unused_1493_ = lean_ctor_get(v_x_1443_, 0);
                            lean_dec(v_unused_1493_);
                            v___x_1457_ = v_x_1443_;
                            v_isShared_1458_ = v_isSharedCheck_1492_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_1443_);
                            v___x_1457_ = lean_box(0);
                            v_isShared_1458_ = v_isSharedCheck_1492_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1494_ = lean_ctor_get(v_x_1443_, 0);
                    v_vs_1495_ = lean_ctor_get(v_x_1443_, 1);
                    v_isSharedCheck_1515_ = (!lean_is_exclusive(v_x_1443_)) as u8;
                    if v_isSharedCheck_1515_ == 0 {
                        v___x_1497_ = v_x_1443_;
                        v_isShared_1498_ = v_isSharedCheck_1515_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_1495_);
                        lean_inc(v_ks_1494_);
                        lean_dec(v_x_1443_);
                        v___x_1497_ = lean_box(0);
                        v_isShared_1498_ = v_isSharedCheck_1515_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1459_ = lean_array_fget(v_es_1448_, v_j_1453_);
                v___x_1460_ = lean_box(0);
                v_xs_x27_1461_ = lean_array_fset(v_es_1448_, v_j_1453_, v___x_1460_);
                match lean_obj_tag(v_v_1459_) {
                    0 => {
                        v_key_1468_ = lean_ctor_get(v_v_1459_, 0);
                        v_val_1469_ = lean_ctor_get(v_v_1459_, 1);
                        v_isSharedCheck_1479_ = (!lean_is_exclusive(v_v_1459_)) as u8;
                        if v_isSharedCheck_1479_ == 0 {
                            v___x_1471_ = v_v_1459_;
                            v_isShared_1472_ = v_isSharedCheck_1479_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_1469_);
                            lean_inc(v_key_1468_);
                            lean_dec(v_v_1459_);
                            v___x_1471_ = lean_box(0);
                            v_isShared_1472_ = v_isSharedCheck_1479_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1480_ = lean_ctor_get(v_v_1459_, 0);
                        v_isSharedCheck_1490_ = (!lean_is_exclusive(v_v_1459_)) as u8;
                        if v_isSharedCheck_1490_ == 0 {
                            v___x_1482_ = v_v_1459_;
                            v_isShared_1483_ = v_isSharedCheck_1490_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_1480_);
                            lean_dec(v_v_1459_);
                            v___x_1482_ = lean_box(0);
                            v_isShared_1483_ = v_isSharedCheck_1490_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1491_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1491_, 0, v_x_1446_);
                        lean_ctor_set(v___x_1491_, 1, v_x_1447_);
                        v___y_1463_ = v___x_1491_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1464_ = lean_array_fset(v_xs_x27_1461_, v_j_1453_, v___y_1463_);
                lean_dec(v_j_1453_);
                if v_isShared_1458_ == 0 {
                    lean_ctor_set(v___x_1457_, 0, v___x_1464_);
                    v___x_1466_ = v___x_1457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
                    v___x_1466_ = v_reuseFailAlloc_1467_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1466_;
            }
            4 => {
                v___x_1473_ = l_Lean_instBEqMVarId_beq(v_x_1446_, v_key_1468_);
                if v___x_1473_ == 0 {
                    lean_del_object(v___x_1471_);
                    v___x_1474_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1468_,
                        v_val_1469_,
                        v_x_1446_,
                        v_x_1447_,
                    );
                    v___x_1475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1475_, 0, v___x_1474_);
                    v___y_1463_ = v___x_1475_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_1469_);
                    lean_dec(v_key_1468_);
                    if v_isShared_1472_ == 0 {
                        lean_ctor_set(v___x_1471_, 1, v_x_1447_);
                        lean_ctor_set(v___x_1471_, 0, v_x_1446_);
                        v___x_1477_ = v___x_1471_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_x_1446_);
                        lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_x_1447_);
                        v___x_1477_ = v_reuseFailAlloc_1478_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1463_ = v___x_1477_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1484_ = lean_usize_shift_right(v_x_1444_, v___x_1449_);
                v___x_1485_ = lean_usize_add(v_x_1445_, v___x_1450_);
                v___x_1486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_node_1480_, v___x_1484_, v___x_1485_, v_x_1446_, v_x_1447_);
                if v_isShared_1483_ == 0 {
                    lean_ctor_set(v___x_1482_, 0, v___x_1486_);
                    v___x_1488_ = v___x_1482_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
                    v___x_1488_ = v_reuseFailAlloc_1489_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1463_ = v___x_1488_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1498_ == 0 {
                    v___x_1500_ = v___x_1497_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_ks_1494_);
                    lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_vs_1495_);
                    v___x_1500_ = v_reuseFailAlloc_1514_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1501_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v___x_1500_, v_x_1446_, v_x_1447_);
                v___x_1509_ = 7usize;
                v___x_1510_ = lean_usize_dec_le(v___x_1509_, v_x_1445_);
                if v___x_1510_ == 0 {
                    v___x_1511_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1501_);
                    v___x_1512_ = lean_unsigned_to_nat(4);
                    v___x_1513_ = lean_nat_dec_lt(v___x_1511_, v___x_1512_);
                    lean_dec(v___x_1511_);
                    v___y_1503_ = v___x_1513_;
                    state = 10;
                    continue;
                } else {
                    v___y_1503_ = v___x_1510_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1503_ == 0 {
                    v_ks_1504_ = lean_ctor_get(v_newNode_1501_, 0);
                    lean_inc_ref(v_ks_1504_);
                    v_vs_1505_ = lean_ctor_get(v_newNode_1501_, 1);
                    lean_inc_ref(v_vs_1505_);
                    lean_dec_ref(v_newNode_1501_);
                    v___x_1506_ = lean_unsigned_to_nat(0);
                    v___x_1507_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___closed__2);
                    v___x_1508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_x_1445_, v_ks_1504_, v_vs_1505_, v___x_1506_, v___x_1507_);
                    lean_dec_ref(v_vs_1505_);
                    lean_dec_ref(v_ks_1504_);
                    return v___x_1508_;
                } else {
                    return v_newNode_1501_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(
    mut v_depth_1516_: usize,
    mut v_keys_1517_: *mut LeanObject,
    mut v_vals_1518_: *mut LeanObject,
    mut v_i_1519_: *mut LeanObject,
    mut v_entries_1520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: u8 = 0;
    let mut v_k_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: u64 = 0;
    let mut v_h_1526_: usize = 0;
    let mut v___x_1527_: usize = 0;
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: usize = 0;
    let mut v___x_1530_: usize = 0;
    let mut v___x_1531_: usize = 0;
    let mut v_h_1532_: usize = 0;
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1521_ = lean_array_get_size(v_keys_1517_);
                v___x_1522_ = lean_nat_dec_lt(v_i_1519_, v___x_1521_);
                if v___x_1522_ == 0 {
                    lean_dec(v_i_1519_);
                    return v_entries_1520_;
                } else {
                    v_k_1523_ = lean_array_fget_borrowed(v_keys_1517_, v_i_1519_);
                    v_v_1524_ = lean_array_fget_borrowed(v_vals_1518_, v_i_1519_);
                    v___x_1525_ = l_Lean_instHashableMVarId_hash(v_k_1523_);
                    v_h_1526_ = lean_uint64_to_usize(v___x_1525_);
                    v___x_1527_ = 5usize;
                    v___x_1528_ = lean_unsigned_to_nat(1);
                    v___x_1529_ = 1usize;
                    v___x_1530_ = lean_usize_sub(v_depth_1516_, v___x_1529_);
                    v___x_1531_ = lean_usize_mul(v___x_1527_, v___x_1530_);
                    v_h_1532_ = lean_usize_shift_right(v_h_1526_, v___x_1531_);
                    v___x_1533_ = lean_nat_add(v_i_1519_, v___x_1528_);
                    lean_dec(v_i_1519_);
                    lean_inc(v_v_1524_);
                    lean_inc(v_k_1523_);
                    v___x_1534_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_entries_1520_, v_h_1532_, v_depth_1516_, v_k_1523_, v_v_1524_);
                    v_i_1519_ = v___x_1533_;
                    v_entries_1520_ = v___x_1534_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_1536_: *mut LeanObject,
    mut v_keys_1537_: *mut LeanObject,
    mut v_vals_1538_: *mut LeanObject,
    mut v_i_1539_: *mut LeanObject,
    mut v_entries_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1541_: usize = 0;
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1541_ = lean_unbox_usize(v_depth_1536_);
    lean_dec(v_depth_1536_);
    v_res_1542_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_1541_, v_keys_1537_, v_vals_1538_, v_i_1539_, v_entries_1540_);
    lean_dec_ref(v_vals_1538_);
    lean_dec_ref(v_keys_1537_);
    return v_res_1542_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_1543_: *mut LeanObject,
    mut v_x_1544_: *mut LeanObject,
    mut v_x_1545_: *mut LeanObject,
    mut v_x_1546_: *mut LeanObject,
    mut v_x_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7757__boxed_1548_: usize = 0;
    let mut v_x_7758__boxed_1549_: usize = 0;
    let mut v_res_1550_: *mut LeanObject = core::ptr::null_mut();
    v_x_7757__boxed_1548_ = lean_unbox_usize(v_x_1544_);
    lean_dec(v_x_1544_);
    v_x_7758__boxed_1549_ = lean_unbox_usize(v_x_1545_);
    lean_dec(v_x_1545_);
    v_res_1550_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_1543_, v_x_7757__boxed_1548_, v_x_7758__boxed_1549_, v_x_1546_, v_x_1547_);
    return v_res_1550_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(
    mut v_x_1551_: *mut LeanObject,
    mut v_x_1552_: *mut LeanObject,
    mut v_x_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1554_: u64 = 0;
    let mut v___x_1555_: usize = 0;
    let mut v___x_1556_: usize = 0;
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_instHashableMVarId_hash(v_x_1552_);
    v___x_1555_ = lean_uint64_to_usize(v___x_1554_);
    v___x_1556_ = 1usize;
    v___x_1557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_1551_, v___x_1555_, v___x_1556_, v_x_1552_, v_x_1553_);
    return v___x_1557_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(
    mut v_mvarId_1558_: *mut LeanObject,
    mut v_val_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1570_: u8 = 0;
    let mut v_depth_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1562_ = lean_st_ref_take(v___y_1560_);
                v_mctx_1563_ = lean_ctor_get(v___x_1562_, 0);
                v_cache_1564_ = lean_ctor_get(v___x_1562_, 1);
                v_zetaDeltaFVarIds_1565_ = lean_ctor_get(v___x_1562_, 2);
                v_postponed_1566_ = lean_ctor_get(v___x_1562_, 3);
                v_diag_1567_ = lean_ctor_get(v___x_1562_, 4);
                v_isSharedCheck_1595_ = (!lean_is_exclusive(v___x_1562_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v___x_1569_ = v___x_1562_;
                    v_isShared_1570_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1567_);
                    lean_inc(v_postponed_1566_);
                    lean_inc(v_zetaDeltaFVarIds_1565_);
                    lean_inc(v_cache_1564_);
                    lean_inc(v_mctx_1563_);
                    lean_dec(v___x_1562_);
                    v___x_1569_ = lean_box(0);
                    v_isShared_1570_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1571_ = lean_ctor_get(v_mctx_1563_, 0);
                v_levelAssignDepth_1572_ = lean_ctor_get(v_mctx_1563_, 1);
                v_lmvarCounter_1573_ = lean_ctor_get(v_mctx_1563_, 2);
                v_mvarCounter_1574_ = lean_ctor_get(v_mctx_1563_, 3);
                v_lDecls_1575_ = lean_ctor_get(v_mctx_1563_, 4);
                v_decls_1576_ = lean_ctor_get(v_mctx_1563_, 5);
                v_userNames_1577_ = lean_ctor_get(v_mctx_1563_, 6);
                v_lAssignment_1578_ = lean_ctor_get(v_mctx_1563_, 7);
                v_eAssignment_1579_ = lean_ctor_get(v_mctx_1563_, 8);
                v_dAssignment_1580_ = lean_ctor_get(v_mctx_1563_, 9);
                v_isSharedCheck_1594_ = (!lean_is_exclusive(v_mctx_1563_)) as u8;
                if v_isSharedCheck_1594_ == 0 {
                    v___x_1582_ = v_mctx_1563_;
                    v_isShared_1583_ = v_isSharedCheck_1594_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1580_);
                    lean_inc(v_eAssignment_1579_);
                    lean_inc(v_lAssignment_1578_);
                    lean_inc(v_userNames_1577_);
                    lean_inc(v_decls_1576_);
                    lean_inc(v_lDecls_1575_);
                    lean_inc(v_mvarCounter_1574_);
                    lean_inc(v_lmvarCounter_1573_);
                    lean_inc(v_levelAssignDepth_1572_);
                    lean_inc(v_depth_1571_);
                    lean_dec(v_mctx_1563_);
                    v___x_1582_ = lean_box(0);
                    v_isShared_1583_ = v_isSharedCheck_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1584_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_eAssignment_1579_, v_mvarId_1558_, v_val_1559_);
                if v_isShared_1583_ == 0 {
                    lean_ctor_set(v___x_1582_, 8, v___x_1584_);
                    v___x_1586_ = v___x_1582_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_depth_1571_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_levelAssignDepth_1572_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_lmvarCounter_1573_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_mvarCounter_1574_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_lDecls_1575_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 5, v_decls_1576_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 6, v_userNames_1577_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 7, v_lAssignment_1578_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 8, v___x_1584_);
                    lean_ctor_set(v_reuseFailAlloc_1593_, 9, v_dAssignment_1580_);
                    v___x_1586_ = v_reuseFailAlloc_1593_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1570_ == 0 {
                    lean_ctor_set(v___x_1569_, 0, v___x_1586_);
                    v___x_1588_ = v___x_1569_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_cache_1564_);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_zetaDeltaFVarIds_1565_);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_postponed_1566_);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_diag_1567_);
                    v___x_1588_ = v_reuseFailAlloc_1592_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1589_ = lean_st_ref_set(v___y_1560_, v___x_1588_);
                v___x_1590_ = lean_box(0);
                v___x_1591_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1591_, 0, v___x_1590_);
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg___boxed(
    mut v_mvarId_1596_: *mut LeanObject,
    mut v_val_1597_: *mut LeanObject,
    mut v___y_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1600_: *mut LeanObject = core::ptr::null_mut();
    v_res_1600_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(
            v_mvarId_1596_,
            v_val_1597_,
            v___y_1598_,
        );
    lean_dec(v___y_1598_);
    return v_res_1600_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(
    mut v_msgData_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
    mut v___y_1603_: *mut LeanObject,
    mut v___y_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    v___x_1607_ = lean_st_ref_get(v___y_1605_);
    v_env_1608_ = lean_ctor_get(v___x_1607_, 0);
    lean_inc_ref(v_env_1608_);
    lean_dec(v___x_1607_);
    v___x_1609_ = lean_st_ref_get(v___y_1603_);
    v_mctx_1610_ = lean_ctor_get(v___x_1609_, 0);
    lean_inc_ref(v_mctx_1610_);
    lean_dec(v___x_1609_);
    v_lctx_1611_ = lean_ctor_get(v___y_1602_, 2);
    v_options_1612_ = lean_ctor_get(v___y_1604_, 2);
    lean_inc_ref(v_options_1612_);
    lean_inc_ref(v_lctx_1611_);
    v___x_1613_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1613_, 0, v_env_1608_);
    lean_ctor_set(v___x_1613_, 1, v_mctx_1610_);
    lean_ctor_set(v___x_1613_, 2, v_lctx_1611_);
    lean_ctor_set(v___x_1613_, 3, v_options_1612_);
    v___x_1614_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1614_, 0, v___x_1613_);
    lean_ctor_set(v___x_1614_, 1, v_msgData_1601_);
    v___x_1615_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1615_, 0, v___x_1614_);
    return v___x_1615_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4___boxed(
    mut v_msgData_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
    mut v___y_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1622_: *mut LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msgData_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
    lean_dec(v___y_1620_);
    lean_dec_ref(v___y_1619_);
    lean_dec(v___y_1618_);
    lean_dec_ref(v___y_1617_);
    return v_res_1622_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(
    mut v_msg_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1634_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1629_ = lean_ctor_get(v___y_1626_, 5);
                v___x_1630_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3_spec__4(v_msg_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
                v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
                v_isSharedCheck_1639_ = (!lean_is_exclusive(v___x_1630_)) as u8;
                if v_isSharedCheck_1639_ == 0 {
                    v___x_1633_ = v___x_1630_;
                    v_isShared_1634_ = v_isSharedCheck_1639_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1631_);
                    lean_dec(v___x_1630_);
                    v___x_1633_ = lean_box(0);
                    v_isShared_1634_ = v_isSharedCheck_1639_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1629_);
                v___x_1635_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1635_, 0, v_ref_1629_);
                lean_ctor_set(v___x_1635_, 1, v_a_1631_);
                if v_isShared_1634_ == 0 {
                    lean_ctor_set_tag(v___x_1633_, 1);
                    lean_ctor_set(v___x_1633_, 0, v___x_1635_);
                    v___x_1637_ = v___x_1633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
                    v___x_1637_ = v_reuseFailAlloc_1638_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg___boxed(
    mut v_msg_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1646_: *mut LeanObject = core::ptr::null_mut();
    v_res_1646_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(
            v_msg_1640_,
            v___y_1641_,
            v___y_1642_,
            v___y_1643_,
            v___y_1644_,
        );
    lean_dec(v___y_1644_);
    lean_dec_ref(v___y_1643_);
    lean_dec(v___y_1642_);
    lean_dec_ref(v___y_1641_);
    return v_res_1646_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    v___x_1653_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__5;
    v___x_1654_ = l_Lean_stringToMessageData(v___x_1653_);
    return v___x_1654_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8()
-> *mut LeanObject {
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__7;
    v___x_1657_ = l_Lean_stringToMessageData(v___x_1656_);
    return v___x_1657_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(
    mut v___x_1658_: *mut LeanObject,
    mut v_snd_1659_: *mut LeanObject,
    mut v___x_1660_: *mut LeanObject,
    mut v___x_1661_: *mut LeanObject,
    mut v___x_1662_: u8,
    mut v___x_1663_: *mut LeanObject,
    mut v_fst_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restHyps_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v_u_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1689_: u8 = 0;
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1720_: u8 = 0;
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1724_: u8 = 0;
    let mut v_reuseFailAlloc_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_isSharedCheck_1728_: u8 = 0;
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___x_1658_) == 1 {
                    v_val_1674_ = lean_ctor_get(v___x_1658_, 0);
                    lean_inc(v_val_1674_);
                    lean_dec_ref_known(v___x_1658_, 1);
                    v___x_1675_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1672_);
                    v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
                    lean_inc(v_a_1676_);
                    lean_dec_ref(v___x_1675_);
                    v_focusHyp_1677_ = lean_ctor_get(v_val_1674_, 0);
                    v_restHyps_1678_ = lean_ctor_get(v_val_1674_, 1);
                    v_proof_1679_ = lean_ctor_get(v_val_1674_, 2);
                    v_isSharedCheck_1728_ = (!lean_is_exclusive(v_val_1674_)) as u8;
                    if v_isSharedCheck_1728_ == 0 {
                        v___x_1681_ = v_val_1674_;
                        v_isShared_1682_ = v_isSharedCheck_1728_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_proof_1679_);
                        lean_inc(v_restHyps_1678_);
                        lean_inc(v_focusHyp_1677_);
                        lean_dec(v_val_1674_);
                        v___x_1681_ = lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1728_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_1664_);
                    lean_dec_ref(v___x_1663_);
                    lean_dec_ref(v_snd_1659_);
                    lean_dec(v___x_1658_);
                    v___x_1729_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6,
                    );
                    v___x_1730_ = l_Lean_MessageData_ofSyntax(v___x_1661_);
                    v___x_1731_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1731_, 0, v___x_1729_);
                    lean_ctor_set(v___x_1731_, 1, v___x_1730_);
                    v___x_1732_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8,
                    );
                    v___x_1733_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1733_, 0, v___x_1731_);
                    lean_ctor_set(v___x_1733_, 1, v___x_1732_);
                    v___x_1734_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_1733_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
                    return v___x_1734_;
                }
            }
            1 => {
                v_u_1683_ = lean_ctor_get(v_snd_1659_, 0);
                v_00_u03c3s_1684_ = lean_ctor_get(v_snd_1659_, 1);
                v_hyps_1685_ = lean_ctor_get(v_snd_1659_, 2);
                v_target_1686_ = lean_ctor_get(v_snd_1659_, 3);
                v_isSharedCheck_1727_ = (!lean_is_exclusive(v_snd_1659_)) as u8;
                if v_isSharedCheck_1727_ == 0 {
                    v___x_1688_ = v_snd_1659_;
                    v_isShared_1689_ = v_isSharedCheck_1727_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_target_1686_);
                    lean_inc(v_hyps_1685_);
                    lean_inc(v_00_u03c3s_1684_);
                    lean_inc(v_u_1683_);
                    lean_dec(v_snd_1659_);
                    v___x_1688_ = lean_box(0);
                    v_isShared_1689_ = v_isSharedCheck_1727_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1690_ = l_Lean_Syntax_getId(v___x_1660_);
                v___x_1691_ = l_Lean_Expr_consumeMData(v_focusHyp_1677_);
                if v_isShared_1682_ == 0 {
                    lean_ctor_set(v___x_1681_, 2, v___x_1691_);
                    lean_ctor_set(v___x_1681_, 1, v_a_1676_);
                    lean_ctor_set(v___x_1681_, 0, v___x_1690_);
                    v___x_1693_ = v___x_1681_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1690_);
                    lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_a_1676_);
                    lean_ctor_set(v_reuseFailAlloc_1726_, 2, v___x_1691_);
                    v___x_1693_ = v_reuseFailAlloc_1726_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_1693_);
                lean_inc_ref(v_00_u03c3s_1684_);
                v___x_1694_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v___x_1661_,
                    v_00_u03c3s_1684_,
                    v___x_1693_,
                    v___x_1662_,
                    v___y_1669_,
                    v___y_1670_,
                    v___y_1671_,
                    v___y_1672_,
                );
                if lean_obj_tag(v___x_1694_) == 0 {
                    lean_dec_ref_known(v___x_1694_, 1);
                    v___x_1695_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1693_);
                    lean_inc_ref(v_hyps_1685_);
                    lean_inc_ref_n(v_00_u03c3s_1684_, 2);
                    lean_inc_n(v_u_1683_, 2);
                    v___x_1696_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                        v_u_1683_,
                        v_00_u03c3s_1684_,
                        v_hyps_1685_,
                        v___x_1695_,
                    );
                    lean_inc_ref(v_target_1686_);
                    if v_isShared_1689_ == 0 {
                        lean_ctor_set(v___x_1688_, 2, v___x_1696_);
                        v___x_1698_ = v___x_1688_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 4, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_u_1683_);
                        lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_00_u03c3s_1684_);
                        lean_ctor_set(v_reuseFailAlloc_1725_, 2, v___x_1696_);
                        lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_target_1686_);
                        v___x_1698_ = v_reuseFailAlloc_1725_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1693_);
                    lean_del_object(v___x_1688_);
                    lean_dec_ref(v_target_1686_);
                    lean_dec_ref(v_hyps_1685_);
                    lean_dec_ref(v_00_u03c3s_1684_);
                    lean_dec(v_u_1683_);
                    lean_dec_ref(v_proof_1679_);
                    lean_dec_ref(v_restHyps_1678_);
                    lean_dec_ref(v_focusHyp_1677_);
                    lean_dec(v_fst_1664_);
                    lean_dec_ref(v___x_1663_);
                    return v___x_1694_;
                }
            }
            4 => {
                v___x_1699_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1698_);
                v___x_1700_ = lean_box(0);
                v___x_1701_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_1699_,
                    v___x_1700_,
                    v___y_1669_,
                    v___y_1670_,
                    v___y_1671_,
                    v___y_1672_,
                );
                if lean_obj_tag(v___x_1701_) == 0 {
                    v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
                    lean_inc_n(v_a_1702_, 2);
                    lean_dec_ref_known(v___x_1701_, 1);
                    v___x_1703_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0;
                    v___x_1704_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1;
                    v___x_1705_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2;
                    v___x_1706_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3;
                    v___x_1707_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__4;
                    v___x_1708_ = l_Lean_Name_mkStr6(
                        v___x_1703_,
                        v___x_1704_,
                        v___x_1705_,
                        v___x_1663_,
                        v___x_1706_,
                        v___x_1707_,
                    );
                    v___x_1709_ = lean_box(0);
                    v___x_1710_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1710_, 0, v_u_1683_);
                    lean_ctor_set(v___x_1710_, 1, v___x_1709_);
                    v___x_1711_ = l_Lean_mkConst(v___x_1708_, v___x_1710_);
                    v___x_1712_ = l_Lean_mkApp7(
                        v___x_1711_,
                        v_00_u03c3s_1684_,
                        v_hyps_1685_,
                        v_restHyps_1678_,
                        v_focusHyp_1677_,
                        v_target_1686_,
                        v_proof_1679_,
                        v_a_1702_,
                    );
                    v___x_1713_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_1664_, v___x_1712_, v___y_1670_);
                    lean_dec_ref(v___x_1713_);
                    v___x_1714_ = l_Lean_Expr_mvarId_x21(v_a_1702_);
                    lean_dec(v_a_1702_);
                    v___x_1715_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1715_, 0, v___x_1714_);
                    lean_ctor_set(v___x_1715_, 1, v___x_1709_);
                    v___x_1716_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_1715_,
                        v___y_1666_,
                        v___y_1669_,
                        v___y_1670_,
                        v___y_1671_,
                        v___y_1672_,
                    );
                    return v___x_1716_;
                } else {
                    lean_dec_ref(v_target_1686_);
                    lean_dec_ref(v_hyps_1685_);
                    lean_dec_ref(v_00_u03c3s_1684_);
                    lean_dec(v_u_1683_);
                    lean_dec_ref(v_proof_1679_);
                    lean_dec_ref(v_restHyps_1678_);
                    lean_dec_ref(v_focusHyp_1677_);
                    lean_dec(v_fst_1664_);
                    lean_dec_ref(v___x_1663_);
                    v_a_1717_ = lean_ctor_get(v___x_1701_, 0);
                    v_isSharedCheck_1724_ = (!lean_is_exclusive(v___x_1701_)) as u8;
                    if v_isSharedCheck_1724_ == 0 {
                        v___x_1719_ = v___x_1701_;
                        v_isShared_1720_ = v_isSharedCheck_1724_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1717_);
                        lean_dec(v___x_1701_);
                        v___x_1719_ = lean_box(0);
                        v_isShared_1720_ = v_isSharedCheck_1724_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_1720_ == 0 {
                    v___x_1722_ = v___x_1719_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
                    v___x_1722_ = v_reuseFailAlloc_1723_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed(
    mut v___x_1735_: *mut LeanObject,
    mut v_snd_1736_: *mut LeanObject,
    mut v___x_1737_: *mut LeanObject,
    mut v___x_1738_: *mut LeanObject,
    mut v___x_1739_: *mut LeanObject,
    mut v___x_1740_: *mut LeanObject,
    mut v_fst_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
    mut v___y_1744_: *mut LeanObject,
    mut v___y_1745_: *mut LeanObject,
    mut v___y_1746_: *mut LeanObject,
    mut v___y_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
    mut v___y_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8063__boxed_1751_: u8 = 0;
    let mut v_res_1752_: *mut LeanObject = core::ptr::null_mut();
    v___x_8063__boxed_1751_ = (lean_unbox(v___x_1739_) as u8);
    v_res_1752_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0(
        v___x_1735_,
        v_snd_1736_,
        v___x_1737_,
        v___x_1738_,
        v___x_8063__boxed_1751_,
        v___x_1740_,
        v_fst_1741_,
        v___y_1742_,
        v___y_1743_,
        v___y_1744_,
        v___y_1745_,
        v___y_1746_,
        v___y_1747_,
        v___y_1748_,
        v___y_1749_,
    );
    lean_dec(v___y_1749_);
    lean_dec_ref(v___y_1748_);
    lean_dec(v___y_1747_);
    lean_dec_ref(v___y_1746_);
    lean_dec(v___y_1745_);
    lean_dec_ref(v___y_1744_);
    lean_dec(v___y_1743_);
    lean_dec_ref(v___y_1742_);
    lean_dec(v___x_1737_);
    return v_res_1752_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(
    mut v_x_1765_: *mut LeanObject,
    mut v_a_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
    mut v_a_1769_: *mut LeanObject,
    mut v_a_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: u8 = 0;
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1775_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2;
                v___x_1776_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4;
                lean_inc(v_x_1765_);
                v___x_1777_ = l_Lean_Syntax_isOfKind(v_x_1765_, v___x_1776_);
                if v___x_1777_ == 0 {
                    lean_dec(v_x_1765_);
                    v___x_1778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                    return v___x_1778_;
                } else {
                    v___x_1779_ = lean_unsigned_to_nat(1);
                    v___x_1780_ = l_Lean_Syntax_getArg(v_x_1765_, v___x_1779_);
                    v___x_1781_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__6;
                    lean_inc(v___x_1780_);
                    v___x_1782_ = l_Lean_Syntax_isOfKind(v___x_1780_, v___x_1781_);
                    if v___x_1782_ == 0 {
                        lean_dec(v___x_1780_);
                        lean_dec(v_x_1765_);
                        v___x_1783_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                        return v___x_1783_;
                    } else {
                        v___x_1784_ = lean_unsigned_to_nat(3);
                        v___x_1785_ = l_Lean_Syntax_getArg(v_x_1765_, v___x_1784_);
                        lean_dec(v_x_1765_);
                        lean_inc(v___x_1785_);
                        v___x_1786_ = l_Lean_Syntax_isOfKind(v___x_1785_, v___x_1781_);
                        if v___x_1786_ == 0 {
                            lean_dec(v___x_1785_);
                            lean_dec(v___x_1780_);
                            v___x_1787_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                            return v___x_1787_;
                        } else {
                            v___x_1788_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
                                v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_,
                                v_a_1772_, v_a_1773_,
                            );
                            if lean_obj_tag(v___x_1788_) == 0 {
                                v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
                                lean_inc(v_a_1789_);
                                lean_dec_ref_known(v___x_1788_, 1);
                                v_fst_1790_ = lean_ctor_get(v_a_1789_, 0);
                                lean_inc_n(v_fst_1790_, 2);
                                v_snd_1791_ = lean_ctor_get(v_a_1789_, 1);
                                lean_inc_n(v_snd_1791_, 2);
                                lean_dec(v_a_1789_);
                                v___x_1792_ = l_Lean_Syntax_getId(v___x_1780_);
                                v___x_1793_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(
                                    v_snd_1791_,
                                    v___x_1792_,
                                );
                                lean_dec(v___x_1792_);
                                v___x_1794_ = lean_box((v___x_1786_) as usize);
                                v___y_1795_ = lean_alloc_closure(
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___boxed
                                        as *mut core::ffi::c_void,
                                    16,
                                    7,
                                );
                                lean_closure_set(v___y_1795_, 0, v___x_1793_);
                                lean_closure_set(v___y_1795_, 1, v_snd_1791_);
                                lean_closure_set(v___y_1795_, 2, v___x_1785_);
                                lean_closure_set(v___y_1795_, 3, v___x_1780_);
                                lean_closure_set(v___y_1795_, 4, v___x_1794_);
                                lean_closure_set(v___y_1795_, 5, v___x_1775_);
                                lean_closure_set(v___y_1795_, 6, v_fst_1790_);
                                v___x_1796_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_1790_, v___y_1795_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
                                return v___x_1796_;
                            } else {
                                lean_dec(v___x_1785_);
                                lean_dec(v___x_1780_);
                                v_a_1797_ = lean_ctor_get(v___x_1788_, 0);
                                v_isSharedCheck_1804_ = (!lean_is_exclusive(v___x_1788_)) as u8;
                                if v_isSharedCheck_1804_ == 0 {
                                    v___x_1799_ = v___x_1788_;
                                    v_isShared_1800_ = v_isSharedCheck_1804_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1797_);
                                    lean_dec(v___x_1788_);
                                    v___x_1799_ = lean_box(0);
                                    v_isShared_1800_ = v_isSharedCheck_1804_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1800_ == 0 {
                    v___x_1802_ = v___x_1799_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
                    v___x_1802_ = v_reuseFailAlloc_1803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1802_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed(
    mut v_x_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
    mut v_a_1809_: *mut LeanObject,
    mut v_a_1810_: *mut LeanObject,
    mut v_a_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1815_: *mut LeanObject = core::ptr::null_mut();
    v_res_1815_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup(
        v_x_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_,
        v_a_1813_,
    );
    lean_dec(v_a_1813_);
    lean_dec_ref(v_a_1812_);
    lean_dec(v_a_1811_);
    lean_dec_ref(v_a_1810_);
    lean_dec(v_a_1809_);
    lean_dec_ref(v_a_1808_);
    lean_dec(v_a_1807_);
    lean_dec_ref(v_a_1806_);
    return v_res_1815_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(
    mut v_mvarId_1816_: *mut LeanObject,
    mut v_val_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1827_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(
            v_mvarId_1816_,
            v_val_1817_,
            v___y_1823_,
        );
    return v___x_1827_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___boxed(
    mut v_mvarId_1828_: *mut LeanObject,
    mut v_val_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
    mut v___y_1833_: *mut LeanObject,
    mut v___y_1834_: *mut LeanObject,
    mut v___y_1835_: *mut LeanObject,
    mut v___y_1836_: *mut LeanObject,
    mut v___y_1837_: *mut LeanObject,
    mut v___y_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2(
        v_mvarId_1828_,
        v_val_1829_,
        v___y_1830_,
        v___y_1831_,
        v___y_1832_,
        v___y_1833_,
        v___y_1834_,
        v___y_1835_,
        v___y_1836_,
        v___y_1837_,
    );
    lean_dec(v___y_1837_);
    lean_dec_ref(v___y_1836_);
    lean_dec(v___y_1835_);
    lean_dec_ref(v___y_1834_);
    lean_dec(v___y_1833_);
    lean_dec_ref(v___y_1832_);
    lean_dec(v___y_1831_);
    lean_dec_ref(v___y_1830_);
    return v_res_1839_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(
    mut v_00_u03b1_1840_: *mut LeanObject,
    mut v_msg_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(
            v_msg_1841_,
            v___y_1846_,
            v___y_1847_,
            v___y_1848_,
            v___y_1849_,
        );
    return v___x_1851_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___boxed(
    mut v_00_u03b1_1852_: *mut LeanObject,
    mut v_msg_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1863_: *mut LeanObject = core::ptr::null_mut();
    v_res_1863_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3(
        v_00_u03b1_1852_,
        v_msg_1853_,
        v___y_1854_,
        v___y_1855_,
        v___y_1856_,
        v___y_1857_,
        v___y_1858_,
        v___y_1859_,
        v___y_1860_,
        v___y_1861_,
    );
    lean_dec(v___y_1861_);
    lean_dec_ref(v___y_1860_);
    lean_dec(v___y_1859_);
    lean_dec_ref(v___y_1858_);
    lean_dec(v___y_1857_);
    lean_dec_ref(v___y_1856_);
    lean_dec(v___y_1855_);
    lean_dec_ref(v___y_1854_);
    return v_res_1863_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2(
    mut v_00_u03b2_1864_: *mut LeanObject,
    mut v_x_1865_: *mut LeanObject,
    mut v_x_1866_: *mut LeanObject,
    mut v_x_1867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2___redArg(v_x_1865_, v_x_1866_, v_x_1867_);
    return v___x_1868_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(
    mut v_00_u03b2_1869_: *mut LeanObject,
    mut v_x_1870_: *mut LeanObject,
    mut v_x_1871_: usize,
    mut v_x_1872_: usize,
    mut v_x_1873_: *mut LeanObject,
    mut v_x_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___redArg(v_x_1870_, v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_1876_: *mut LeanObject,
    mut v_x_1877_: *mut LeanObject,
    mut v_x_1878_: *mut LeanObject,
    mut v_x_1879_: *mut LeanObject,
    mut v_x_1880_: *mut LeanObject,
    mut v_x_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_8400__boxed_1882_: usize = 0;
    let mut v_x_8401__boxed_1883_: usize = 0;
    let mut v_res_1884_: *mut LeanObject = core::ptr::null_mut();
    v_x_8400__boxed_1882_ = lean_unbox_usize(v_x_1878_);
    lean_dec(v_x_1878_);
    v_x_8401__boxed_1883_ = lean_unbox_usize(v_x_1879_);
    lean_dec(v_x_1879_);
    v_res_1884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4(v_00_u03b2_1876_, v_x_1877_, v_x_8400__boxed_1882_, v_x_8401__boxed_1883_, v_x_1880_, v_x_1881_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7(
    mut v_00_u03b2_1885_: *mut LeanObject,
    mut v_n_1886_: *mut LeanObject,
    mut v_k_1887_: *mut LeanObject,
    mut v_v_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    v___x_1889_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7___redArg(v_n_1886_, v_k_1887_, v_v_1888_);
    return v___x_1889_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(
    mut v_00_u03b2_1890_: *mut LeanObject,
    mut v_depth_1891_: usize,
    mut v_keys_1892_: *mut LeanObject,
    mut v_vals_1893_: *mut LeanObject,
    mut v_heq_1894_: *mut LeanObject,
    mut v_i_1895_: *mut LeanObject,
    mut v_entries_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_1891_, v_keys_1892_, v_vals_1893_, v_i_1895_, v_entries_1896_);
    return v___x_1897_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_1898_: *mut LeanObject,
    mut v_depth_1899_: *mut LeanObject,
    mut v_keys_1900_: *mut LeanObject,
    mut v_vals_1901_: *mut LeanObject,
    mut v_heq_1902_: *mut LeanObject,
    mut v_i_1903_: *mut LeanObject,
    mut v_entries_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1905_: usize = 0;
    let mut v_res_1906_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1905_ = lean_unbox_usize(v_depth_1899_);
    lean_dec(v_depth_1899_);
    v_res_1906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_1898_, v_depth_boxed_1905_, v_keys_1900_, v_vals_1901_, v_heq_1902_, v_i_1903_, v_entries_1904_);
    lean_dec_ref(v_vals_1901_);
    lean_dec_ref(v_keys_1900_);
    return v_res_1906_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8(
    mut v_00_u03b2_1907_: *mut LeanObject,
    mut v_x_1908_: *mut LeanObject,
    mut v_x_1909_: *mut LeanObject,
    mut v_x_1910_: *mut LeanObject,
    mut v_x_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_1908_, v_x_1909_, v_x_1910_, v_x_1911_);
    return v___x_1912_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1()
-> *mut LeanObject {
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    v___x_1924_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1925_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__4;
    v___x_1926_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___closed__3;
    v___x_1927_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1928_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1924_,
        v___x_1925_,
        v___x_1926_,
        v___x_1927_,
    );
    return v___x_1928_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1___boxed(
    mut v_a_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1930_: *mut LeanObject = core::ptr::null_mut();
    v_res_1930_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
    return v_res_1930_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(
    mut v___x_1932_: *mut LeanObject,
    mut v_00_u03c3s_1933_: *mut LeanObject,
    mut v___x_1934_: u8,
    mut v_u_1935_: *mut LeanObject,
    mut v_hyps_1936_: *mut LeanObject,
    mut v___x_1937_: *mut LeanObject,
    mut v_target_1938_: *mut LeanObject,
    mut v___x_1939_: *mut LeanObject,
    mut v___x_1940_: *mut LeanObject,
    mut v___x_1941_: *mut LeanObject,
    mut v___x_1942_: *mut LeanObject,
    mut v___x_1943_: *mut LeanObject,
    mut v_fst_1944_: *mut LeanObject,
    mut v_H_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1962_: u8 = 0;
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2009_: u8 = 0;
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_isSharedCheck_2012_: u8 = 0;
    let mut v_unused_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1955_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_1953_);
                v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
                lean_inc(v_a_1956_);
                lean_dec_ref(v___x_1955_);
                v___x_1957_ = l_Lean_Syntax_getId(v___x_1932_);
                lean_inc_ref(v_H_1945_);
                v___x_1958_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1958_, 0, v___x_1957_);
                lean_ctor_set(v___x_1958_, 1, v_a_1956_);
                lean_ctor_set(v___x_1958_, 2, v_H_1945_);
                lean_inc_ref(v___x_1958_);
                lean_inc_ref(v_00_u03c3s_1933_);
                v___x_1959_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v___x_1932_,
                    v_00_u03c3s_1933_,
                    v___x_1958_,
                    v___x_1934_,
                    v___y_1950_,
                    v___y_1951_,
                    v___y_1952_,
                    v___y_1953_,
                );
                if lean_obj_tag(v___x_1959_) == 0 {
                    v_isSharedCheck_2012_ = (!lean_is_exclusive(v___x_1959_)) as u8;
                    if v_isSharedCheck_2012_ == 0 {
                        v_unused_2013_ = lean_ctor_get(v___x_1959_, 0);
                        lean_dec(v_unused_2013_);
                        v___x_1961_ = v___x_1959_;
                        v_isShared_1962_ = v_isSharedCheck_2012_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_1959_);
                        v___x_1961_ = lean_box(0);
                        v_isShared_1962_ = v_isSharedCheck_2012_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_1958_, 3);
                    lean_dec_ref(v_H_1945_);
                    lean_dec(v_fst_1944_);
                    lean_dec(v___x_1943_);
                    lean_dec_ref(v___x_1942_);
                    lean_dec_ref(v___x_1941_);
                    lean_dec_ref(v___x_1940_);
                    lean_dec_ref(v___x_1939_);
                    lean_dec_ref(v_target_1938_);
                    lean_dec(v___x_1937_);
                    lean_dec_ref(v_hyps_1936_);
                    lean_dec(v_u_1935_);
                    lean_dec_ref(v_00_u03c3s_1933_);
                    return v___x_1959_;
                }
            }
            1 => {
                v___x_1963_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1958_);
                lean_inc_ref(v___x_1963_);
                lean_inc_ref(v_hyps_1936_);
                lean_inc_ref(v_00_u03c3s_1933_);
                lean_inc(v_u_1935_);
                v___x_1964_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_u_1935_,
                    v_00_u03c3s_1933_,
                    v_hyps_1936_,
                    v___x_1963_,
                );
                v_fst_1965_ = lean_ctor_get(v___x_1964_, 0);
                v_snd_1966_ = lean_ctor_get(v___x_1964_, 1);
                v_isSharedCheck_2011_ = (!lean_is_exclusive(v___x_1964_)) as u8;
                if v_isSharedCheck_2011_ == 0 {
                    v___x_1968_ = v___x_1964_;
                    v_isShared_1969_ = v_isSharedCheck_2011_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_1966_);
                    lean_inc(v_fst_1965_);
                    lean_dec(v___x_1964_);
                    v___x_1968_ = lean_box(0);
                    v_isShared_1969_ = v_isSharedCheck_2011_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_hyps_1936_);
                lean_inc_ref(v_00_u03c3s_1933_);
                lean_inc(v_u_1935_);
                v___x_1970_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1970_, 0, v_u_1935_);
                lean_ctor_set(v___x_1970_, 1, v_00_u03c3s_1933_);
                lean_ctor_set(v___x_1970_, 2, v_hyps_1936_);
                lean_ctor_set(v___x_1970_, 3, v_H_1945_);
                v___x_1971_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1970_);
                if v_isShared_1962_ == 0 {
                    lean_ctor_set_tag(v___x_1961_, 1);
                    lean_ctor_set(v___x_1961_, 0, v___x_1971_);
                    v___x_1973_ = v___x_1961_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_1971_);
                    v___x_1973_ = v_reuseFailAlloc_2010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1974_ = 0;
                v___x_1975_ = l_Lean_Elab_Tactic_elabTermEnsuringType(
                    v___x_1937_,
                    v___x_1973_,
                    v___x_1974_,
                    v___y_1946_,
                    v___y_1947_,
                    v___y_1948_,
                    v___y_1949_,
                    v___y_1950_,
                    v___y_1951_,
                    v___y_1952_,
                    v___y_1953_,
                );
                if lean_obj_tag(v___x_1975_) == 0 {
                    v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
                    lean_inc(v_a_1976_);
                    lean_dec_ref_known(v___x_1975_, 1);
                    lean_inc_ref(v_target_1938_);
                    lean_inc(v_fst_1965_);
                    lean_inc_ref(v_00_u03c3s_1933_);
                    v___x_1977_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_1977_, 0, v_u_1935_);
                    lean_ctor_set(v___x_1977_, 1, v_00_u03c3s_1933_);
                    lean_ctor_set(v___x_1977_, 2, v_fst_1965_);
                    lean_ctor_set(v___x_1977_, 3, v_target_1938_);
                    v___x_1978_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1977_);
                    v___x_1979_ = lean_box(0);
                    v___x_1980_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_1978_,
                        v___x_1979_,
                        v___y_1950_,
                        v___y_1951_,
                        v___y_1952_,
                        v___y_1953_,
                    );
                    if lean_obj_tag(v___x_1980_) == 0 {
                        v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
                        lean_inc_n(v_a_1981_, 2);
                        lean_dec_ref_known(v___x_1980_, 1);
                        v___x_1982_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3;
                        v___x_1983_ =
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___closed__0;
                        v___x_1984_ = l_Lean_Name_mkStr6(
                            v___x_1939_,
                            v___x_1940_,
                            v___x_1941_,
                            v___x_1942_,
                            v___x_1982_,
                            v___x_1983_,
                        );
                        v___x_1985_ = l_Lean_mkConst(v___x_1984_, v___x_1943_);
                        v___x_1986_ = l_Lean_mkApp8(
                            v___x_1985_,
                            v_00_u03c3s_1933_,
                            v_hyps_1936_,
                            v___x_1963_,
                            v_fst_1965_,
                            v_target_1938_,
                            v_snd_1966_,
                            v_a_1976_,
                            v_a_1981_,
                        );
                        v___x_1987_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_1944_, v___x_1986_, v___y_1951_);
                        lean_dec_ref(v___x_1987_);
                        v___x_1988_ = l_Lean_Expr_mvarId_x21(v_a_1981_);
                        lean_dec(v_a_1981_);
                        v___x_1989_ = lean_box(0);
                        if v_isShared_1969_ == 0 {
                            lean_ctor_set_tag(v___x_1968_, 1);
                            lean_ctor_set(v___x_1968_, 1, v___x_1989_);
                            lean_ctor_set(v___x_1968_, 0, v___x_1988_);
                            v___x_1991_ = v___x_1968_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1988_);
                            lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1989_);
                            v___x_1991_ = v_reuseFailAlloc_1993_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1976_);
                        lean_del_object(v___x_1968_);
                        lean_dec(v_snd_1966_);
                        lean_dec(v_fst_1965_);
                        lean_dec_ref(v___x_1963_);
                        lean_dec(v_fst_1944_);
                        lean_dec(v___x_1943_);
                        lean_dec_ref(v___x_1942_);
                        lean_dec_ref(v___x_1941_);
                        lean_dec_ref(v___x_1940_);
                        lean_dec_ref(v___x_1939_);
                        lean_dec_ref(v_target_1938_);
                        lean_dec_ref(v_hyps_1936_);
                        lean_dec_ref(v_00_u03c3s_1933_);
                        v_a_1994_ = lean_ctor_get(v___x_1980_, 0);
                        v_isSharedCheck_2001_ = (!lean_is_exclusive(v___x_1980_)) as u8;
                        if v_isSharedCheck_2001_ == 0 {
                            v___x_1996_ = v___x_1980_;
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1994_);
                            lean_dec(v___x_1980_);
                            v___x_1996_ = lean_box(0);
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1968_);
                    lean_dec(v_snd_1966_);
                    lean_dec(v_fst_1965_);
                    lean_dec_ref(v___x_1963_);
                    lean_dec(v_fst_1944_);
                    lean_dec(v___x_1943_);
                    lean_dec_ref(v___x_1942_);
                    lean_dec_ref(v___x_1941_);
                    lean_dec_ref(v___x_1940_);
                    lean_dec_ref(v___x_1939_);
                    lean_dec_ref(v_target_1938_);
                    lean_dec_ref(v_hyps_1936_);
                    lean_dec(v_u_1935_);
                    lean_dec_ref(v_00_u03c3s_1933_);
                    v_a_2002_ = lean_ctor_get(v___x_1975_, 0);
                    v_isSharedCheck_2009_ = (!lean_is_exclusive(v___x_1975_)) as u8;
                    if v_isSharedCheck_2009_ == 0 {
                        v___x_2004_ = v___x_1975_;
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2002_);
                        lean_dec(v___x_1975_);
                        v___x_2004_ = lean_box(0);
                        v_isShared_2005_ = v_isSharedCheck_2009_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1992_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_1991_,
                    v___y_1947_,
                    v___y_1950_,
                    v___y_1951_,
                    v___y_1952_,
                    v___y_1953_,
                );
                return v___x_1992_;
            }
            5 => {
                if v_isShared_1997_ == 0 {
                    v___x_1999_ = v___x_1996_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
                    v___x_1999_ = v_reuseFailAlloc_2000_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1999_;
            }
            7 => {
                if v_isShared_2005_ == 0 {
                    v___x_2007_ = v___x_2004_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
                    v___x_2007_ = v_reuseFailAlloc_2008_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2007_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2014_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3s_2015_: *mut LeanObject = *_args.add(1);
    let mut v___x_2016_: *mut LeanObject = *_args.add(2);
    let mut v_u_2017_: *mut LeanObject = *_args.add(3);
    let mut v_hyps_2018_: *mut LeanObject = *_args.add(4);
    let mut v___x_2019_: *mut LeanObject = *_args.add(5);
    let mut v_target_2020_: *mut LeanObject = *_args.add(6);
    let mut v___x_2021_: *mut LeanObject = *_args.add(7);
    let mut v___x_2022_: *mut LeanObject = *_args.add(8);
    let mut v___x_2023_: *mut LeanObject = *_args.add(9);
    let mut v___x_2024_: *mut LeanObject = *_args.add(10);
    let mut v___x_2025_: *mut LeanObject = *_args.add(11);
    let mut v_fst_2026_: *mut LeanObject = *_args.add(12);
    let mut v_H_2027_: *mut LeanObject = *_args.add(13);
    let mut v___y_2028_: *mut LeanObject = *_args.add(14);
    let mut v___y_2029_: *mut LeanObject = *_args.add(15);
    let mut v___y_2030_: *mut LeanObject = *_args.add(16);
    let mut v___y_2031_: *mut LeanObject = *_args.add(17);
    let mut v___y_2032_: *mut LeanObject = *_args.add(18);
    let mut v___y_2033_: *mut LeanObject = *_args.add(19);
    let mut v___y_2034_: *mut LeanObject = *_args.add(20);
    let mut v___y_2035_: *mut LeanObject = *_args.add(21);
    let mut v___y_2036_: *mut LeanObject = *_args.add(22);
    let mut v___x_2878__boxed_2037_: u8 = 0;
    let mut v_res_2038_: *mut LeanObject = core::ptr::null_mut();
    v___x_2878__boxed_2037_ = (lean_unbox(v___x_2016_) as u8);
    v_res_2038_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0(
        v___x_2014_,
        v_00_u03c3s_2015_,
        v___x_2878__boxed_2037_,
        v_u_2017_,
        v_hyps_2018_,
        v___x_2019_,
        v_target_2020_,
        v___x_2021_,
        v___x_2022_,
        v___x_2023_,
        v___x_2024_,
        v___x_2025_,
        v_fst_2026_,
        v_H_2027_,
        v___y_2028_,
        v___y_2029_,
        v___y_2030_,
        v___y_2031_,
        v___y_2032_,
        v___y_2033_,
        v___y_2034_,
        v___y_2035_,
    );
    lean_dec(v___y_2035_);
    lean_dec_ref(v___y_2034_);
    lean_dec(v___y_2033_);
    lean_dec_ref(v___y_2032_);
    lean_dec(v___y_2031_);
    lean_dec_ref(v___y_2030_);
    lean_dec(v___y_2029_);
    lean_dec_ref(v___y_2028_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(
    mut v_ty_x3f_2039_: *mut LeanObject,
    mut v___x_2040_: *mut LeanObject,
    mut v___f_2041_: *mut LeanObject,
    mut v___y_2042_: *mut LeanObject,
    mut v___y_2043_: *mut LeanObject,
    mut v___y_2044_: *mut LeanObject,
    mut v___y_2045_: *mut LeanObject,
    mut v___y_2046_: *mut LeanObject,
    mut v___y_2047_: *mut LeanObject,
    mut v___y_2048_: *mut LeanObject,
    mut v___y_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2064_: u8 = 0;
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2068_: u8 = 0;
    let mut v_reuseFailAlloc_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ty_x3f_2039_) == 1 {
                    v_val_2051_ = lean_ctor_get(v_ty_x3f_2039_, 0);
                    v_isSharedCheck_2070_ = (!lean_is_exclusive(v_ty_x3f_2039_)) as u8;
                    if v_isSharedCheck_2070_ == 0 {
                        v___x_2053_ = v_ty_x3f_2039_;
                        v_isShared_2054_ = v_isSharedCheck_2070_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2051_);
                        lean_dec(v_ty_x3f_2039_);
                        v___x_2053_ = lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2070_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_ty_x3f_2039_);
                    v___x_2071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2071_, 0, v___x_2040_);
                    v___x_2072_ = 0;
                    v___x_2073_ = lean_box(0);
                    v___x_2074_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_2071_,
                        v___x_2072_,
                        v___x_2073_,
                        v___y_2046_,
                        v___y_2047_,
                        v___y_2048_,
                        v___y_2049_,
                    );
                    if lean_obj_tag(v___x_2074_) == 0 {
                        v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
                        lean_inc(v_a_2075_);
                        lean_dec_ref_known(v___x_2074_, 1);
                        lean_inc(v___y_2049_);
                        lean_inc_ref(v___y_2048_);
                        lean_inc(v___y_2047_);
                        lean_inc_ref(v___y_2046_);
                        lean_inc(v___y_2045_);
                        lean_inc_ref(v___y_2044_);
                        lean_inc(v___y_2043_);
                        lean_inc_ref(v___y_2042_);
                        v___x_2076_ = lean_apply_10(
                            v___f_2041_,
                            v_a_2075_,
                            v___y_2042_,
                            v___y_2043_,
                            v___y_2044_,
                            v___y_2045_,
                            v___y_2046_,
                            v___y_2047_,
                            v___y_2048_,
                            v___y_2049_,
                            lean_box(0),
                        );
                        return v___x_2076_;
                    } else {
                        lean_dec_ref(v___f_2041_);
                        v_a_2077_ = lean_ctor_get(v___x_2074_, 0);
                        v_isSharedCheck_2084_ = (!lean_is_exclusive(v___x_2074_)) as u8;
                        if v_isSharedCheck_2084_ == 0 {
                            v___x_2079_ = v___x_2074_;
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2077_);
                            lean_dec(v___x_2074_);
                            v___x_2079_ = lean_box(0);
                            v_isShared_2080_ = v_isSharedCheck_2084_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2054_ == 0 {
                    lean_ctor_set(v___x_2053_, 0, v___x_2040_);
                    v___x_2056_ = v___x_2053_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2040_);
                    v___x_2056_ = v_reuseFailAlloc_2069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2057_ = 0;
                v___x_2058_ = l_Lean_Elab_Tactic_elabTerm(
                    v_val_2051_,
                    v___x_2056_,
                    v___x_2057_,
                    v___y_2042_,
                    v___y_2043_,
                    v___y_2044_,
                    v___y_2045_,
                    v___y_2046_,
                    v___y_2047_,
                    v___y_2048_,
                    v___y_2049_,
                );
                if lean_obj_tag(v___x_2058_) == 0 {
                    v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
                    lean_inc(v_a_2059_);
                    lean_dec_ref_known(v___x_2058_, 1);
                    lean_inc(v___y_2049_);
                    lean_inc_ref(v___y_2048_);
                    lean_inc(v___y_2047_);
                    lean_inc_ref(v___y_2046_);
                    lean_inc(v___y_2045_);
                    lean_inc_ref(v___y_2044_);
                    lean_inc(v___y_2043_);
                    lean_inc_ref(v___y_2042_);
                    v___x_2060_ = lean_apply_10(
                        v___f_2041_,
                        v_a_2059_,
                        v___y_2042_,
                        v___y_2043_,
                        v___y_2044_,
                        v___y_2045_,
                        v___y_2046_,
                        v___y_2047_,
                        v___y_2048_,
                        v___y_2049_,
                        lean_box(0),
                    );
                    return v___x_2060_;
                } else {
                    lean_dec_ref(v___f_2041_);
                    v_a_2061_ = lean_ctor_get(v___x_2058_, 0);
                    v_isSharedCheck_2068_ = (!lean_is_exclusive(v___x_2058_)) as u8;
                    if v_isSharedCheck_2068_ == 0 {
                        v___x_2063_ = v___x_2058_;
                        v_isShared_2064_ = v_isSharedCheck_2068_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2061_);
                        lean_dec(v___x_2058_);
                        v___x_2063_ = lean_box(0);
                        v_isShared_2064_ = v_isSharedCheck_2068_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2064_ == 0 {
                    v___x_2066_ = v___x_2063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
                    v___x_2066_ = v_reuseFailAlloc_2067_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2066_;
            }
            5 => {
                if v_isShared_2080_ == 0 {
                    v___x_2082_ = v___x_2079_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
                    v___x_2082_ = v_reuseFailAlloc_2083_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed(
    mut v_ty_x3f_2085_: *mut LeanObject,
    mut v___x_2086_: *mut LeanObject,
    mut v___f_2087_: *mut LeanObject,
    mut v___y_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
    mut v___y_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
    mut v___y_2095_: *mut LeanObject,
    mut v___y_2096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2097_: *mut LeanObject = core::ptr::null_mut();
    v_res_2097_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1(
        v_ty_x3f_2085_,
        v___x_2086_,
        v___f_2087_,
        v___y_2088_,
        v___y_2089_,
        v___y_2090_,
        v___y_2091_,
        v___y_2092_,
        v___y_2093_,
        v___y_2094_,
        v___y_2095_,
    );
    lean_dec(v___y_2095_);
    lean_dec_ref(v___y_2094_);
    lean_dec(v___y_2093_);
    lean_dec_ref(v___y_2092_);
    lean_dec(v___y_2091_);
    lean_dec_ref(v___y_2090_);
    lean_dec(v___y_2089_);
    lean_dec_ref(v___y_2088_);
    return v_res_2097_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(
    mut v_x_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
    mut v_a_2111_: *mut LeanObject,
    mut v_a_2112_: *mut LeanObject,
    mut v_a_2113_: *mut LeanObject,
    mut v_a_2114_: *mut LeanObject,
    mut v_a_2115_: *mut LeanObject,
    mut v_a_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v_u_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_a_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u8 = 0;
    let mut v___x_2173_: u8 = 0;
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2118_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2;
                v___x_2119_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1;
                lean_inc(v_x_2108_);
                v___x_2120_ = l_Lean_Syntax_isOfKind(v_x_2108_, v___x_2119_);
                if v___x_2120_ == 0 {
                    lean_dec(v_x_2108_);
                    v___x_2121_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                    return v___x_2121_;
                } else {
                    v___x_2122_ = lean_unsigned_to_nat(1);
                    v___x_2123_ = l_Lean_Syntax_getArg(v_x_2108_, v___x_2122_);
                    v___x_2170_ = lean_unsigned_to_nat(2);
                    v___x_2171_ = l_Lean_Syntax_getArg(v_x_2108_, v___x_2170_);
                    v___x_2172_ = l_Lean_Syntax_isNone(v___x_2171_);
                    if v___x_2172_ == 0 {
                        lean_inc(v___x_2171_);
                        v___x_2173_ = l_Lean_Syntax_matchesNull(v___x_2171_, v___x_2170_);
                        if v___x_2173_ == 0 {
                            lean_dec(v___x_2171_);
                            lean_dec(v___x_2123_);
                            lean_dec(v_x_2108_);
                            v___x_2174_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                            return v___x_2174_;
                        } else {
                            v_ty_x3f_2175_ = l_Lean_Syntax_getArg(v___x_2171_, v___x_2122_);
                            lean_dec(v___x_2171_);
                            v___x_2176_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2176_, 0, v_ty_x3f_2175_);
                            v_ty_x3f_2125_ = v___x_2176_;
                            v___y_2126_ = v_a_2109_;
                            v___y_2127_ = v_a_2110_;
                            v___y_2128_ = v_a_2111_;
                            v___y_2129_ = v_a_2112_;
                            v___y_2130_ = v_a_2113_;
                            v___y_2131_ = v_a_2114_;
                            v___y_2132_ = v_a_2115_;
                            v___y_2133_ = v_a_2116_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2171_);
                        v___x_2177_ = lean_box(0);
                        v_ty_x3f_2125_ = v___x_2177_;
                        v___y_2126_ = v_a_2109_;
                        v___y_2127_ = v_a_2110_;
                        v___y_2128_ = v_a_2111_;
                        v___y_2129_ = v_a_2112_;
                        v___y_2130_ = v_a_2113_;
                        v___y_2131_ = v_a_2114_;
                        v___y_2132_ = v_a_2115_;
                        v___y_2133_ = v_a_2116_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2134_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
                    v___y_2126_,
                    v___y_2127_,
                    v___y_2128_,
                    v___y_2129_,
                    v___y_2130_,
                    v___y_2131_,
                    v___y_2132_,
                    v___y_2133_,
                );
                if lean_obj_tag(v___x_2134_) == 0 {
                    v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
                    lean_inc(v_a_2135_);
                    lean_dec_ref_known(v___x_2134_, 1);
                    v_snd_2136_ = lean_ctor_get(v_a_2135_, 1);
                    v_fst_2137_ = lean_ctor_get(v_a_2135_, 0);
                    v_isSharedCheck_2161_ = (!lean_is_exclusive(v_a_2135_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2139_ = v_a_2135_;
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_2136_);
                        lean_inc(v_fst_2137_);
                        lean_dec(v_a_2135_);
                        v___x_2139_ = lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_ty_x3f_2125_);
                    lean_dec(v___x_2123_);
                    lean_dec(v_x_2108_);
                    v_a_2162_ = lean_ctor_get(v___x_2134_, 0);
                    v_isSharedCheck_2169_ = (!lean_is_exclusive(v___x_2134_)) as u8;
                    if v_isSharedCheck_2169_ == 0 {
                        v___x_2164_ = v___x_2134_;
                        v_isShared_2165_ = v_isSharedCheck_2169_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2162_);
                        lean_dec(v___x_2134_);
                        v___x_2164_ = lean_box(0);
                        v_isShared_2165_ = v_isSharedCheck_2169_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_u_2141_ = lean_ctor_get(v_snd_2136_, 0);
                lean_inc_n(v_u_2141_, 2);
                v_00_u03c3s_2142_ = lean_ctor_get(v_snd_2136_, 1);
                lean_inc_ref(v_00_u03c3s_2142_);
                v_hyps_2143_ = lean_ctor_get(v_snd_2136_, 2);
                lean_inc_ref(v_hyps_2143_);
                v_target_2144_ = lean_ctor_get(v_snd_2136_, 3);
                lean_inc_ref(v_target_2144_);
                lean_dec(v_snd_2136_);
                v___x_2145_ = lean_unsigned_to_nat(4);
                v___x_2146_ = l_Lean_Syntax_getArg(v_x_2108_, v___x_2145_);
                lean_dec(v_x_2108_);
                v___x_2147_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0;
                v___x_2148_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1;
                v___x_2149_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2;
                v___x_2150_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2;
                v___x_2151_ = lean_box(0);
                if v_isShared_2140_ == 0 {
                    lean_ctor_set_tag(v___x_2139_, 1);
                    lean_ctor_set(v___x_2139_, 1, v___x_2151_);
                    lean_ctor_set(v___x_2139_, 0, v_u_2141_);
                    v___x_2153_ = v___x_2139_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_u_2141_);
                    lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2151_);
                    v___x_2153_ = v_reuseFailAlloc_2160_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2154_ = lean_box((v___x_2120_) as usize);
                lean_inc(v_fst_2137_);
                lean_inc_ref(v___x_2153_);
                lean_inc_ref(v_00_u03c3s_2142_);
                v___f_2155_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__0___boxed
                        as *mut core::ffi::c_void,
                    23,
                    13,
                );
                lean_closure_set(v___f_2155_, 0, v___x_2123_);
                lean_closure_set(v___f_2155_, 1, v_00_u03c3s_2142_);
                lean_closure_set(v___f_2155_, 2, v___x_2154_);
                lean_closure_set(v___f_2155_, 3, v_u_2141_);
                lean_closure_set(v___f_2155_, 4, v_hyps_2143_);
                lean_closure_set(v___f_2155_, 5, v___x_2146_);
                lean_closure_set(v___f_2155_, 6, v_target_2144_);
                lean_closure_set(v___f_2155_, 7, v___x_2147_);
                lean_closure_set(v___f_2155_, 8, v___x_2148_);
                lean_closure_set(v___f_2155_, 9, v___x_2149_);
                lean_closure_set(v___f_2155_, 10, v___x_2118_);
                lean_closure_set(v___f_2155_, 11, v___x_2153_);
                lean_closure_set(v___f_2155_, 12, v_fst_2137_);
                v___x_2156_ = l_Lean_mkConst(v___x_2150_, v___x_2153_);
                v___x_2157_ = l_Lean_Expr_app___override(v___x_2156_, v_00_u03c3s_2142_);
                v___y_2158_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___lam__1___boxed
                        as *mut core::ffi::c_void,
                    12,
                    3,
                );
                lean_closure_set(v___y_2158_, 0, v_ty_x3f_2125_);
                lean_closure_set(v___y_2158_, 1, v___x_2157_);
                lean_closure_set(v___y_2158_, 2, v___f_2155_);
                v___x_2159_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_2137_, v___y_2158_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
                return v___x_2159_;
            }
            4 => {
                if v_isShared_2165_ == 0 {
                    v___x_2167_ = v___x_2164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed(
    mut v_x_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
    mut v_a_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
    mut v_a_2182_: *mut LeanObject,
    mut v_a_2183_: *mut LeanObject,
    mut v_a_2184_: *mut LeanObject,
    mut v_a_2185_: *mut LeanObject,
    mut v_a_2186_: *mut LeanObject,
    mut v_a_2187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2188_: *mut LeanObject = core::ptr::null_mut();
    v_res_2188_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave(
        v_x_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_,
        v_a_2186_,
    );
    lean_dec(v_a_2186_);
    lean_dec_ref(v_a_2185_);
    lean_dec(v_a_2184_);
    lean_dec_ref(v_a_2183_);
    lean_dec(v_a_2182_);
    lean_dec_ref(v_a_2181_);
    lean_dec(v_a_2180_);
    lean_dec_ref(v_a_2179_);
    return v_res_2188_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1()
-> *mut LeanObject {
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    v___x_2198_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2199_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__1;
    v___x_2200_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___closed__1;
    v___x_2201_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2202_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2198_,
        v___x_2199_,
        v___x_2200_,
        v___x_2201_,
    );
    return v___x_2202_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1___boxed(
    mut v_a_2203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2204_: *mut LeanObject = core::ptr::null_mut();
    v_res_2204_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
    return v_res_2204_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(
    mut v___x_2206_: *mut LeanObject,
    mut v_u_2207_: *mut LeanObject,
    mut v___x_2208_: *mut LeanObject,
    mut v___x_2209_: *mut LeanObject,
    mut v_00_u03c3s_2210_: *mut LeanObject,
    mut v___x_2211_: u8,
    mut v_hyps_2212_: *mut LeanObject,
    mut v___x_2213_: *mut LeanObject,
    mut v_target_2214_: *mut LeanObject,
    mut v___x_2215_: *mut LeanObject,
    mut v_fst_2216_: *mut LeanObject,
    mut v_ty_x3f_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2230_: u8 = 0;
    let mut v_focusHyp_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restHyps_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_H_x27_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2271_: u8 = 0;
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2292_: u8 = 0;
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2296_: u8 = 0;
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_a_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2301_: u8 = 0;
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2305_: u8 = 0;
    let mut v_reuseFailAlloc_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2313_: u8 = 0;
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2326_: u8 = 0;
    let mut v_reuseFailAlloc_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: u8 = 0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_isSharedCheck_2342_: u8 = 0;
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___x_2206_) == 1 {
                    v_val_2227_ = lean_ctor_get(v___x_2206_, 0);
                    v_isSharedCheck_2343_ = (!lean_is_exclusive(v___x_2206_)) as u8;
                    if v_isSharedCheck_2343_ == 0 {
                        v___x_2229_ = v___x_2206_;
                        v_isShared_2230_ = v_isSharedCheck_2343_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2227_);
                        lean_dec(v___x_2206_);
                        v___x_2229_ = lean_box(0);
                        v_isShared_2230_ = v_isSharedCheck_2343_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_ty_x3f_2217_);
                    lean_dec(v_fst_2216_);
                    lean_dec_ref(v___x_2215_);
                    lean_dec_ref(v_target_2214_);
                    lean_dec(v___x_2213_);
                    lean_dec_ref(v_hyps_2212_);
                    lean_dec_ref(v_00_u03c3s_2210_);
                    lean_dec(v___x_2208_);
                    lean_dec(v_u_2207_);
                    lean_dec(v___x_2206_);
                    v___x_2344_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__6,
                    );
                    v___x_2345_ = l_Lean_MessageData_ofSyntax(v___x_2209_);
                    v___x_2346_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2346_, 0, v___x_2344_);
                    lean_ctor_set(v___x_2346_, 1, v___x_2345_);
                    v___x_2347_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__8,
                    );
                    v___x_2348_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2348_, 0, v___x_2346_);
                    lean_ctor_set(v___x_2348_, 1, v___x_2347_);
                    v___x_2349_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__3___redArg(v___x_2348_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
                    return v___x_2349_;
                }
            }
            1 => {
                v_focusHyp_2231_ = lean_ctor_get(v_val_2227_, 0);
                v_restHyps_2232_ = lean_ctor_get(v_val_2227_, 1);
                v_proof_2233_ = lean_ctor_get(v_val_2227_, 2);
                v_isSharedCheck_2342_ = (!lean_is_exclusive(v_val_2227_)) as u8;
                if v_isSharedCheck_2342_ == 0 {
                    v___x_2235_ = v_val_2227_;
                    v_isShared_2236_ = v_isSharedCheck_2342_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_proof_2233_);
                    lean_inc(v_restHyps_2232_);
                    lean_inc(v_focusHyp_2231_);
                    lean_dec(v_val_2227_);
                    v___x_2235_ = lean_box(0);
                    v_isShared_2236_ = v_isSharedCheck_2342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2237_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__0;
                v___x_2238_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__1;
                v___x_2239_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__2;
                v___x_2240_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMHave___closed__2;
                v___x_2241_ = lean_box(0);
                lean_inc(v_u_2207_);
                v___x_2242_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2242_, 0, v_u_2207_);
                lean_ctor_set(v___x_2242_, 1, v___x_2241_);
                lean_inc_ref(v___x_2242_);
                v___x_2308_ = l_Lean_mkConst(v___x_2240_, v___x_2242_);
                lean_inc_ref(v_00_u03c3s_2210_);
                v___x_2309_ = l_Lean_Expr_app___override(v___x_2308_, v_00_u03c3s_2210_);
                if lean_obj_tag(v_ty_x3f_2217_) == 1 {
                    v_val_2310_ = lean_ctor_get(v_ty_x3f_2217_, 0);
                    v_isSharedCheck_2328_ = (!lean_is_exclusive(v_ty_x3f_2217_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v___x_2312_ = v_ty_x3f_2217_;
                        v_isShared_2313_ = v_isSharedCheck_2328_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_val_2310_);
                        lean_dec(v_ty_x3f_2217_);
                        v___x_2312_ = lean_box(0);
                        v_isShared_2313_ = v_isSharedCheck_2328_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v_ty_x3f_2217_);
                    v___x_2329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2329_, 0, v___x_2309_);
                    v___x_2330_ = 0;
                    v___x_2331_ = lean_box(0);
                    v___x_2332_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_2329_,
                        v___x_2330_,
                        v___x_2331_,
                        v___y_2222_,
                        v___y_2223_,
                        v___y_2224_,
                        v___y_2225_,
                    );
                    if lean_obj_tag(v___x_2332_) == 0 {
                        v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
                        lean_inc(v_a_2333_);
                        lean_dec_ref_known(v___x_2332_, 1);
                        v_H_x27_2244_ = v_a_2333_;
                        v___y_2245_ = v___y_2218_;
                        v___y_2246_ = v___y_2219_;
                        v___y_2247_ = v___y_2220_;
                        v___y_2248_ = v___y_2221_;
                        v___y_2249_ = v___y_2222_;
                        v___y_2250_ = v___y_2223_;
                        v___y_2251_ = v___y_2224_;
                        v___y_2252_ = v___y_2225_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_2242_, 2);
                        lean_del_object(v___x_2235_);
                        lean_dec_ref(v_proof_2233_);
                        lean_dec_ref(v_restHyps_2232_);
                        lean_dec_ref(v_focusHyp_2231_);
                        lean_del_object(v___x_2229_);
                        lean_dec(v_fst_2216_);
                        lean_dec_ref(v___x_2215_);
                        lean_dec_ref(v_target_2214_);
                        lean_dec(v___x_2213_);
                        lean_dec_ref(v_hyps_2212_);
                        lean_dec_ref(v_00_u03c3s_2210_);
                        lean_dec(v___x_2209_);
                        lean_dec(v___x_2208_);
                        lean_dec(v_u_2207_);
                        v_a_2334_ = lean_ctor_get(v___x_2332_, 0);
                        v_isSharedCheck_2341_ = (!lean_is_exclusive(v___x_2332_)) as u8;
                        if v_isSharedCheck_2341_ == 0 {
                            v___x_2336_ = v___x_2332_;
                            v_isShared_2337_ = v_isSharedCheck_2341_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_2334_);
                            lean_dec(v___x_2332_);
                            v___x_2336_ = lean_box(0);
                            v_isShared_2337_ = v_isSharedCheck_2341_;
                            state = 16;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2253_ = l_Lean_mkFreshId___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__1___redArg(v___y_2252_);
                v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
                lean_inc(v_a_2254_);
                lean_dec_ref(v___x_2253_);
                lean_inc_ref(v_H_x27_2244_);
                if v_isShared_2236_ == 0 {
                    lean_ctor_set(v___x_2235_, 2, v_H_x27_2244_);
                    lean_ctor_set(v___x_2235_, 1, v_a_2254_);
                    lean_ctor_set(v___x_2235_, 0, v___x_2208_);
                    v___x_2256_ = v___x_2235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2208_);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_a_2254_);
                    lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_H_x27_2244_);
                    v___x_2256_ = v_reuseFailAlloc_2307_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v___x_2256_);
                lean_inc_ref(v_00_u03c3s_2210_);
                v___x_2257_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                    v___x_2209_,
                    v_00_u03c3s_2210_,
                    v___x_2256_,
                    v___x_2211_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                if lean_obj_tag(v___x_2257_) == 0 {
                    lean_dec_ref_known(v___x_2257_, 1);
                    lean_inc_ref(v_hyps_2212_);
                    lean_inc_ref(v_00_u03c3s_2210_);
                    lean_inc(v_u_2207_);
                    v___x_2258_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_2258_, 0, v_u_2207_);
                    lean_ctor_set(v___x_2258_, 1, v_00_u03c3s_2210_);
                    lean_ctor_set(v___x_2258_, 2, v_hyps_2212_);
                    lean_ctor_set(v___x_2258_, 3, v_H_x27_2244_);
                    v___x_2259_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2258_);
                    if v_isShared_2230_ == 0 {
                        lean_ctor_set(v___x_2229_, 0, v___x_2259_);
                        v___x_2261_ = v___x_2229_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2259_);
                        v___x_2261_ = v_reuseFailAlloc_2306_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2256_);
                    lean_dec_ref(v_H_x27_2244_);
                    lean_dec_ref_known(v___x_2242_, 2);
                    lean_dec_ref(v_proof_2233_);
                    lean_dec_ref(v_restHyps_2232_);
                    lean_dec_ref(v_focusHyp_2231_);
                    lean_del_object(v___x_2229_);
                    lean_dec(v_fst_2216_);
                    lean_dec_ref(v___x_2215_);
                    lean_dec_ref(v_target_2214_);
                    lean_dec(v___x_2213_);
                    lean_dec_ref(v_hyps_2212_);
                    lean_dec_ref(v_00_u03c3s_2210_);
                    lean_dec(v_u_2207_);
                    return v___x_2257_;
                }
            }
            5 => {
                v___x_2262_ = 0;
                v___x_2263_ = l_Lean_Elab_Tactic_elabTermEnsuringType(
                    v___x_2213_,
                    v___x_2261_,
                    v___x_2262_,
                    v___y_2245_,
                    v___y_2246_,
                    v___y_2247_,
                    v___y_2248_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                if lean_obj_tag(v___x_2263_) == 0 {
                    v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
                    lean_inc(v_a_2264_);
                    lean_dec_ref_known(v___x_2263_, 1);
                    v___x_2265_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_2256_);
                    lean_inc_ref(v___x_2265_);
                    lean_inc_ref(v_restHyps_2232_);
                    lean_inc_ref(v_00_u03c3s_2210_);
                    lean_inc(v_u_2207_);
                    v___x_2266_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                        v_u_2207_,
                        v_00_u03c3s_2210_,
                        v_restHyps_2232_,
                        v___x_2265_,
                    );
                    v_fst_2267_ = lean_ctor_get(v___x_2266_, 0);
                    v_snd_2268_ = lean_ctor_get(v___x_2266_, 1);
                    v_isSharedCheck_2297_ = (!lean_is_exclusive(v___x_2266_)) as u8;
                    if v_isSharedCheck_2297_ == 0 {
                        v___x_2270_ = v___x_2266_;
                        v_isShared_2271_ = v_isSharedCheck_2297_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2268_);
                        lean_inc(v_fst_2267_);
                        lean_dec(v___x_2266_);
                        v___x_2270_ = lean_box(0);
                        v_isShared_2271_ = v_isSharedCheck_2297_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2256_);
                    lean_dec_ref_known(v___x_2242_, 2);
                    lean_dec_ref(v_proof_2233_);
                    lean_dec_ref(v_restHyps_2232_);
                    lean_dec_ref(v_focusHyp_2231_);
                    lean_dec(v_fst_2216_);
                    lean_dec_ref(v___x_2215_);
                    lean_dec_ref(v_target_2214_);
                    lean_dec_ref(v_hyps_2212_);
                    lean_dec_ref(v_00_u03c3s_2210_);
                    lean_dec(v_u_2207_);
                    v_a_2298_ = lean_ctor_get(v___x_2263_, 0);
                    v_isSharedCheck_2305_ = (!lean_is_exclusive(v___x_2263_)) as u8;
                    if v_isSharedCheck_2305_ == 0 {
                        v___x_2300_ = v___x_2263_;
                        v_isShared_2301_ = v_isSharedCheck_2305_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2298_);
                        lean_dec(v___x_2263_);
                        v___x_2300_ = lean_box(0);
                        v_isShared_2301_ = v_isSharedCheck_2305_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                lean_inc_ref(v_target_2214_);
                lean_inc(v_fst_2267_);
                lean_inc_ref(v_00_u03c3s_2210_);
                v___x_2272_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_2272_, 0, v_u_2207_);
                lean_ctor_set(v___x_2272_, 1, v_00_u03c3s_2210_);
                lean_ctor_set(v___x_2272_, 2, v_fst_2267_);
                lean_ctor_set(v___x_2272_, 3, v_target_2214_);
                v___x_2273_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_2272_);
                v___x_2274_ = lean_box(0);
                v___x_2275_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_2273_,
                    v___x_2274_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                if lean_obj_tag(v___x_2275_) == 0 {
                    v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
                    lean_inc_n(v_a_2276_, 2);
                    lean_dec_ref_known(v___x_2275_, 1);
                    v___x_2277_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___lam__0___closed__3;
                    v___x_2278_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___closed__0;
                    v___x_2279_ = l_Lean_Name_mkStr6(
                        v___x_2237_,
                        v___x_2238_,
                        v___x_2239_,
                        v___x_2215_,
                        v___x_2277_,
                        v___x_2278_,
                    );
                    v___x_2280_ = l_Lean_mkConst(v___x_2279_, v___x_2242_);
                    v___x_2281_ = l_Lean_mkApp10(
                        v___x_2280_,
                        v_00_u03c3s_2210_,
                        v_restHyps_2232_,
                        v_focusHyp_2231_,
                        v___x_2265_,
                        v_hyps_2212_,
                        v_fst_2267_,
                        v_target_2214_,
                        v_proof_2233_,
                        v_snd_2268_,
                        v_a_2264_,
                    );
                    v___x_2282_ = l_Lean_Expr_app___override(v___x_2281_, v_a_2276_);
                    v___x_2283_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__2___redArg(v_fst_2216_, v___x_2282_, v___y_2250_);
                    lean_dec_ref(v___x_2283_);
                    v___x_2284_ = l_Lean_Expr_mvarId_x21(v_a_2276_);
                    lean_dec(v_a_2276_);
                    if v_isShared_2271_ == 0 {
                        lean_ctor_set_tag(v___x_2270_, 1);
                        lean_ctor_set(v___x_2270_, 1, v___x_2241_);
                        lean_ctor_set(v___x_2270_, 0, v___x_2284_);
                        v___x_2286_ = v___x_2270_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2284_);
                        lean_ctor_set(v_reuseFailAlloc_2288_, 1, v___x_2241_);
                        v___x_2286_ = v_reuseFailAlloc_2288_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2270_);
                    lean_dec(v_snd_2268_);
                    lean_dec(v_fst_2267_);
                    lean_dec_ref(v___x_2265_);
                    lean_dec(v_a_2264_);
                    lean_dec_ref_known(v___x_2242_, 2);
                    lean_dec_ref(v_proof_2233_);
                    lean_dec_ref(v_restHyps_2232_);
                    lean_dec_ref(v_focusHyp_2231_);
                    lean_dec(v_fst_2216_);
                    lean_dec_ref(v___x_2215_);
                    lean_dec_ref(v_target_2214_);
                    lean_dec_ref(v_hyps_2212_);
                    lean_dec_ref(v_00_u03c3s_2210_);
                    v_a_2289_ = lean_ctor_get(v___x_2275_, 0);
                    v_isSharedCheck_2296_ = (!lean_is_exclusive(v___x_2275_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2291_ = v___x_2275_;
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2289_);
                        lean_dec(v___x_2275_);
                        v___x_2291_ = lean_box(0);
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2287_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_2286_,
                    v___y_2246_,
                    v___y_2249_,
                    v___y_2250_,
                    v___y_2251_,
                    v___y_2252_,
                );
                return v___x_2287_;
            }
            8 => {
                if v_isShared_2292_ == 0 {
                    v___x_2294_ = v___x_2291_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
                    v___x_2294_ = v_reuseFailAlloc_2295_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2294_;
            }
            10 => {
                if v_isShared_2301_ == 0 {
                    v___x_2303_ = v___x_2300_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
                    v___x_2303_ = v_reuseFailAlloc_2304_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2303_;
            }
            12 => {
                if v_isShared_2313_ == 0 {
                    lean_ctor_set(v___x_2312_, 0, v___x_2309_);
                    v___x_2315_ = v___x_2312_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2309_);
                    v___x_2315_ = v_reuseFailAlloc_2327_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2316_ = 0;
                v___x_2317_ = l_Lean_Elab_Tactic_elabTerm(
                    v_val_2310_,
                    v___x_2315_,
                    v___x_2316_,
                    v___y_2218_,
                    v___y_2219_,
                    v___y_2220_,
                    v___y_2221_,
                    v___y_2222_,
                    v___y_2223_,
                    v___y_2224_,
                    v___y_2225_,
                );
                if lean_obj_tag(v___x_2317_) == 0 {
                    v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
                    lean_inc(v_a_2318_);
                    lean_dec_ref_known(v___x_2317_, 1);
                    v_H_x27_2244_ = v_a_2318_;
                    v___y_2245_ = v___y_2218_;
                    v___y_2246_ = v___y_2219_;
                    v___y_2247_ = v___y_2220_;
                    v___y_2248_ = v___y_2221_;
                    v___y_2249_ = v___y_2222_;
                    v___y_2250_ = v___y_2223_;
                    v___y_2251_ = v___y_2224_;
                    v___y_2252_ = v___y_2225_;
                    state = 3;
                    continue;
                } else {
                    lean_dec_ref_known(v___x_2242_, 2);
                    lean_del_object(v___x_2235_);
                    lean_dec_ref(v_proof_2233_);
                    lean_dec_ref(v_restHyps_2232_);
                    lean_dec_ref(v_focusHyp_2231_);
                    lean_del_object(v___x_2229_);
                    lean_dec(v_fst_2216_);
                    lean_dec_ref(v___x_2215_);
                    lean_dec_ref(v_target_2214_);
                    lean_dec(v___x_2213_);
                    lean_dec_ref(v_hyps_2212_);
                    lean_dec_ref(v_00_u03c3s_2210_);
                    lean_dec(v___x_2209_);
                    lean_dec(v___x_2208_);
                    lean_dec(v_u_2207_);
                    v_a_2319_ = lean_ctor_get(v___x_2317_, 0);
                    v_isSharedCheck_2326_ = (!lean_is_exclusive(v___x_2317_)) as u8;
                    if v_isSharedCheck_2326_ == 0 {
                        v___x_2321_ = v___x_2317_;
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2319_);
                        lean_dec(v___x_2317_);
                        v___x_2321_ = lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2326_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2322_ == 0 {
                    v___x_2324_ = v___x_2321_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
                    v___x_2324_ = v_reuseFailAlloc_2325_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2324_;
            }
            16 => {
                if v_isShared_2337_ == 0 {
                    v___x_2339_ = v___x_2336_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
                    v___x_2339_ = v_reuseFailAlloc_2340_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = *_args.add(0);
    let mut v_u_2351_: *mut LeanObject = *_args.add(1);
    let mut v___x_2352_: *mut LeanObject = *_args.add(2);
    let mut v___x_2353_: *mut LeanObject = *_args.add(3);
    let mut v_00_u03c3s_2354_: *mut LeanObject = *_args.add(4);
    let mut v___x_2355_: *mut LeanObject = *_args.add(5);
    let mut v_hyps_2356_: *mut LeanObject = *_args.add(6);
    let mut v___x_2357_: *mut LeanObject = *_args.add(7);
    let mut v_target_2358_: *mut LeanObject = *_args.add(8);
    let mut v___x_2359_: *mut LeanObject = *_args.add(9);
    let mut v_fst_2360_: *mut LeanObject = *_args.add(10);
    let mut v_ty_x3f_2361_: *mut LeanObject = *_args.add(11);
    let mut v___y_2362_: *mut LeanObject = *_args.add(12);
    let mut v___y_2363_: *mut LeanObject = *_args.add(13);
    let mut v___y_2364_: *mut LeanObject = *_args.add(14);
    let mut v___y_2365_: *mut LeanObject = *_args.add(15);
    let mut v___y_2366_: *mut LeanObject = *_args.add(16);
    let mut v___y_2367_: *mut LeanObject = *_args.add(17);
    let mut v___y_2368_: *mut LeanObject = *_args.add(18);
    let mut v___y_2369_: *mut LeanObject = *_args.add(19);
    let mut v___y_2370_: *mut LeanObject = *_args.add(20);
    let mut v___x_3617__boxed_2371_: u8 = 0;
    let mut v_res_2372_: *mut LeanObject = core::ptr::null_mut();
    v___x_3617__boxed_2371_ = (lean_unbox(v___x_2355_) as u8);
    v_res_2372_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0(
        v___x_2350_,
        v_u_2351_,
        v___x_2352_,
        v___x_2353_,
        v_00_u03c3s_2354_,
        v___x_3617__boxed_2371_,
        v_hyps_2356_,
        v___x_2357_,
        v_target_2358_,
        v___x_2359_,
        v_fst_2360_,
        v_ty_x3f_2361_,
        v___y_2362_,
        v___y_2363_,
        v___y_2364_,
        v___y_2365_,
        v___y_2366_,
        v___y_2367_,
        v___y_2368_,
        v___y_2369_,
    );
    lean_dec(v___y_2369_);
    lean_dec_ref(v___y_2368_);
    lean_dec(v___y_2367_);
    lean_dec_ref(v___y_2366_);
    lean_dec(v___y_2365_);
    lean_dec_ref(v___y_2364_);
    lean_dec(v___y_2363_);
    lean_dec_ref(v___y_2362_);
    return v_res_2372_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(
    mut v_x_2379_: *mut LeanObject,
    mut v_a_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
    mut v_a_2383_: *mut LeanObject,
    mut v_a_2384_: *mut LeanObject,
    mut v_a_2385_: *mut LeanObject,
    mut v_a_2386_: *mut LeanObject,
    mut v_a_2387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2389_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMDup___closed__2;
                v___x_2390_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1;
                lean_inc(v_x_2379_);
                v___x_2391_ = l_Lean_Syntax_isOfKind(v_x_2379_, v___x_2390_);
                if v___x_2391_ == 0 {
                    lean_dec(v_x_2379_);
                    v___x_2392_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                    return v___x_2392_;
                } else {
                    v___x_2393_ = lean_unsigned_to_nat(1);
                    v___x_2394_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2393_);
                    v___x_2428_ = lean_unsigned_to_nat(2);
                    v___x_2429_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2428_);
                    v___x_2430_ = l_Lean_Syntax_isNone(v___x_2429_);
                    if v___x_2430_ == 0 {
                        lean_inc(v___x_2429_);
                        v___x_2431_ = l_Lean_Syntax_matchesNull(v___x_2429_, v___x_2428_);
                        if v___x_2431_ == 0 {
                            lean_dec(v___x_2429_);
                            lean_dec(v___x_2394_);
                            lean_dec(v_x_2379_);
                            v___x_2432_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__0___redArg();
                            return v___x_2432_;
                        } else {
                            v_ty_x3f_2433_ = l_Lean_Syntax_getArg(v___x_2429_, v___x_2393_);
                            lean_dec(v___x_2429_);
                            v___x_2434_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2434_, 0, v_ty_x3f_2433_);
                            v_ty_x3f_2396_ = v___x_2434_;
                            v___y_2397_ = v_a_2380_;
                            v___y_2398_ = v_a_2381_;
                            v___y_2399_ = v_a_2382_;
                            v___y_2400_ = v_a_2383_;
                            v___y_2401_ = v_a_2384_;
                            v___y_2402_ = v_a_2385_;
                            v___y_2403_ = v_a_2386_;
                            v___y_2404_ = v_a_2387_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2429_);
                        v___x_2435_ = lean_box(0);
                        v_ty_x3f_2396_ = v___x_2435_;
                        v___y_2397_ = v_a_2380_;
                        v___y_2398_ = v_a_2381_;
                        v___y_2399_ = v_a_2382_;
                        v___y_2400_ = v_a_2383_;
                        v___y_2401_ = v_a_2384_;
                        v___y_2402_ = v_a_2385_;
                        v___y_2403_ = v_a_2386_;
                        v___y_2404_ = v_a_2387_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2405_ = l_Lean_Elab_Tactic_Do_ProofMode_ensureMGoal(
                    v___y_2397_,
                    v___y_2398_,
                    v___y_2399_,
                    v___y_2400_,
                    v___y_2401_,
                    v___y_2402_,
                    v___y_2403_,
                    v___y_2404_,
                );
                if lean_obj_tag(v___x_2405_) == 0 {
                    v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
                    lean_inc(v_a_2406_);
                    lean_dec_ref_known(v___x_2405_, 1);
                    v_snd_2407_ = lean_ctor_get(v_a_2406_, 1);
                    lean_inc(v_snd_2407_);
                    v_fst_2408_ = lean_ctor_get(v_a_2406_, 0);
                    lean_inc_n(v_fst_2408_, 2);
                    lean_dec(v_a_2406_);
                    v_u_2409_ = lean_ctor_get(v_snd_2407_, 0);
                    lean_inc(v_u_2409_);
                    v_00_u03c3s_2410_ = lean_ctor_get(v_snd_2407_, 1);
                    lean_inc_ref(v_00_u03c3s_2410_);
                    v_hyps_2411_ = lean_ctor_get(v_snd_2407_, 2);
                    lean_inc_ref(v_hyps_2411_);
                    v_target_2412_ = lean_ctor_get(v_snd_2407_, 3);
                    lean_inc_ref(v_target_2412_);
                    v___x_2413_ = lean_unsigned_to_nat(4);
                    v___x_2414_ = l_Lean_Syntax_getArg(v_x_2379_, v___x_2413_);
                    lean_dec(v_x_2379_);
                    v___x_2415_ = l_Lean_Syntax_getId(v___x_2394_);
                    v___x_2416_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_snd_2407_, v___x_2415_);
                    v___x_2417_ = lean_box((v___x_2391_) as usize);
                    v___y_2418_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___lam__0___boxed
                            as *mut core::ffi::c_void,
                        21,
                        12,
                    );
                    lean_closure_set(v___y_2418_, 0, v___x_2416_);
                    lean_closure_set(v___y_2418_, 1, v_u_2409_);
                    lean_closure_set(v___y_2418_, 2, v___x_2415_);
                    lean_closure_set(v___y_2418_, 3, v___x_2394_);
                    lean_closure_set(v___y_2418_, 4, v_00_u03c3s_2410_);
                    lean_closure_set(v___y_2418_, 5, v___x_2417_);
                    lean_closure_set(v___y_2418_, 6, v_hyps_2411_);
                    lean_closure_set(v___y_2418_, 7, v___x_2414_);
                    lean_closure_set(v___y_2418_, 8, v_target_2412_);
                    lean_closure_set(v___y_2418_, 9, v___x_2389_);
                    lean_closure_set(v___y_2418_, 10, v_fst_2408_);
                    lean_closure_set(v___y_2418_, 11, v_ty_x3f_2396_);
                    v___x_2419_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMDup_spec__4___redArg(v_fst_2408_, v___y_2418_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
                    return v___x_2419_;
                } else {
                    lean_dec(v_ty_x3f_2396_);
                    lean_dec(v___x_2394_);
                    lean_dec(v_x_2379_);
                    v_a_2420_ = lean_ctor_get(v___x_2405_, 0);
                    v_isSharedCheck_2427_ = (!lean_is_exclusive(v___x_2405_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v___x_2422_ = v___x_2405_;
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2420_);
                        lean_dec(v___x_2405_);
                        v___x_2422_ = lean_box(0);
                        v_isShared_2423_ = v_isSharedCheck_2427_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2423_ == 0 {
                    v___x_2425_ = v___x_2422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed(
    mut v_x_2436_: *mut LeanObject,
    mut v_a_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
    mut v_a_2442_: *mut LeanObject,
    mut v_a_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2446_: *mut LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace(
        v_x_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_,
        v_a_2444_,
    );
    lean_dec(v_a_2444_);
    lean_dec_ref(v_a_2443_);
    lean_dec(v_a_2442_);
    lean_dec_ref(v_a_2441_);
    lean_dec(v_a_2440_);
    lean_dec_ref(v_a_2439_);
    lean_dec(v_a_2438_);
    lean_dec_ref(v_a_2437_);
    return v_res_2446_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1()
-> *mut LeanObject {
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    v___x_2456_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2457_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___closed__1;
    v___x_2458_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___closed__1;
    v___x_2459_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMReplace___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_2460_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2456_,
        v___x_2457_,
        v___x_2458_,
        v___x_2459_,
    );
    return v___x_2460_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1___boxed(
    mut v_a_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2462_: *mut LeanObject = core::ptr::null_mut();
    v_res_2462_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
    return v_res_2462_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMDup___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMDup__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMHave___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMHave__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Have_0__Lean_Elab_Tactic_Do_ProofMode_elabMReplace___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMReplace__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Have(builtin);
}
