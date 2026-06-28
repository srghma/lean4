// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Clear
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.Focus
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr6, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
    l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal,
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp7, l_Lean_mkConst,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
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
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0_value: LeanStringObject<
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value: LeanStringObject<
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2_value: LeanStringObject<
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3_value: LeanStringObject<
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
    m_data: [67, 108, 101, 97, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4_value: LeanStringObject<
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
    m_data: [99, 108, 101, 97, 114, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        110, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value: LeanStringObject<7> =
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
        m_data: [109, 99, 108, 101, 97, 114, 0],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value)
                as *mut LeanObject,
            18344149449936419494 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__3_value)
                as *mut LeanObject,
            12602713191225532779 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value: LeanStringObject<6> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__5_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 67, 108, 101, 97, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__1_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__2_value) as *mut LeanObject,17134313240879321948 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    v___x_671_ = lean_box(0);
    v___x_672_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_673_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_673_, 0, v___x_672_);
    lean_ctor_set(v___x_673_, 1, v___x_671_);
    return v___x_673_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    v___x_675_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___closed__0);
    v___x_676_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_676_, 0, v___x_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg___boxed(
    mut v___y_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_678_: *mut LeanObject = core::ptr::null_mut();
    v_res_678_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
    return v_res_678_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0(
    mut v_00_u03b1_679_: *mut LeanObject,
    mut v___y_680_: *mut LeanObject,
    mut v___y_681_: *mut LeanObject,
    mut v___y_682_: *mut LeanObject,
    mut v___y_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
    mut v___y_685_: *mut LeanObject,
    mut v___y_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    v___x_689_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
    return v___x_689_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___boxed(
    mut v_00_u03b1_690_: *mut LeanObject,
    mut v___y_691_: *mut LeanObject,
    mut v___y_692_: *mut LeanObject,
    mut v___y_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
    mut v___y_696_: *mut LeanObject,
    mut v___y_697_: *mut LeanObject,
    mut v___y_698_: *mut LeanObject,
    mut v___y_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_700_: *mut LeanObject = core::ptr::null_mut();
    v_res_700_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0(v_00_u03b1_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
    lean_dec(v___y_698_);
    lean_dec_ref(v___y_697_);
    lean_dec(v___y_696_);
    lean_dec_ref(v___y_695_);
    lean_dec(v___y_694_);
    lean_dec_ref(v___y_693_);
    lean_dec(v___y_692_);
    lean_dec_ref(v___y_691_);
    return v_res_700_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(
    mut v_e_701_: *mut LeanObject,
    mut v___y_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_718_: u8 = 0;
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v_unused_725_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_704_ = l_Lean_Expr_hasMVar(v_e_701_);
                if v___x_704_ == 0 {
                    v___x_705_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_705_, 0, v_e_701_);
                    return v___x_705_;
                } else {
                    v___x_706_ = lean_st_ref_get(v___y_702_);
                    v_mctx_707_ = lean_ctor_get(v___x_706_, 0);
                    lean_inc_ref(v_mctx_707_);
                    lean_dec(v___x_706_);
                    v___x_708_ = l_Lean_instantiateMVarsCore(v_mctx_707_, v_e_701_);
                    v_fst_709_ = lean_ctor_get(v___x_708_, 0);
                    lean_inc(v_fst_709_);
                    v_snd_710_ = lean_ctor_get(v___x_708_, 1);
                    lean_inc(v_snd_710_);
                    lean_dec_ref(v___x_708_);
                    v___x_711_ = lean_st_ref_take(v___y_702_);
                    v_cache_712_ = lean_ctor_get(v___x_711_, 1);
                    v_zetaDeltaFVarIds_713_ = lean_ctor_get(v___x_711_, 2);
                    v_postponed_714_ = lean_ctor_get(v___x_711_, 3);
                    v_diag_715_ = lean_ctor_get(v___x_711_, 4);
                    v_isSharedCheck_724_ = (!lean_is_exclusive(v___x_711_)) as u8;
                    if v_isSharedCheck_724_ == 0 {
                        v_unused_725_ = lean_ctor_get(v___x_711_, 0);
                        lean_dec(v_unused_725_);
                        v___x_717_ = v___x_711_;
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_715_);
                        lean_inc(v_postponed_714_);
                        lean_inc(v_zetaDeltaFVarIds_713_);
                        lean_inc(v_cache_712_);
                        lean_dec(v___x_711_);
                        v___x_717_ = lean_box(0);
                        v_isShared_718_ = v_isSharedCheck_724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_718_ == 0 {
                    lean_ctor_set(v___x_717_, 0, v_snd_710_);
                    v___x_720_ = v___x_717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_723_, 0, v_snd_710_);
                    lean_ctor_set(v_reuseFailAlloc_723_, 1, v_cache_712_);
                    lean_ctor_set(v_reuseFailAlloc_723_, 2, v_zetaDeltaFVarIds_713_);
                    lean_ctor_set(v_reuseFailAlloc_723_, 3, v_postponed_714_);
                    lean_ctor_set(v_reuseFailAlloc_723_, 4, v_diag_715_);
                    v___x_720_ = v_reuseFailAlloc_723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_721_ = lean_st_ref_set(v___y_702_, v___x_720_);
                v___x_722_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_722_, 0, v_fst_709_);
                return v___x_722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg___boxed(
    mut v_e_726_: *mut LeanObject,
    mut v___y_727_: *mut LeanObject,
    mut v___y_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_729_: *mut LeanObject = core::ptr::null_mut();
    v_res_729_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(
            v_e_726_, v___y_727_,
        );
    lean_dec(v___y_727_);
    return v_res_729_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1(
    mut v_e_730_: *mut LeanObject,
    mut v___y_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
    mut v___y_738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    v___x_740_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(
            v_e_730_, v___y_736_,
        );
    return v___x_740_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___boxed(
    mut v_e_741_: *mut LeanObject,
    mut v___y_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
    mut v___y_750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_751_: *mut LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1(
        v_e_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_,
        v___y_748_, v___y_749_,
    );
    lean_dec(v___y_749_);
    lean_dec_ref(v___y_748_);
    lean_dec(v___y_747_);
    lean_dec_ref(v___y_746_);
    lean_dec(v___y_745_);
    lean_dec_ref(v___y_744_);
    lean_dec(v___y_743_);
    lean_dec_ref(v___y_742_);
    return v_res_751_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0(
    mut v_x_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
    mut v___y_755_: *mut LeanObject,
    mut v___y_756_: *mut LeanObject,
    mut v___y_757_: *mut LeanObject,
    mut v___y_758_: *mut LeanObject,
    mut v___y_759_: *mut LeanObject,
    mut v___y_760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_756_);
    lean_inc_ref(v___y_755_);
    lean_inc(v___y_754_);
    lean_inc_ref(v___y_753_);
    v___x_762_ = lean_apply_9(
        v_x_752_,
        v___y_753_,
        v___y_754_,
        v___y_755_,
        v___y_756_,
        v___y_757_,
        v___y_758_,
        v___y_759_,
        v___y_760_,
        lean_box(0),
    );
    return v___x_762_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0___boxed(
    mut v_x_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_773_: *mut LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0(v_x_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
    lean_dec(v___y_767_);
    lean_dec_ref(v___y_766_);
    lean_dec(v___y_765_);
    lean_dec_ref(v___y_764_);
    return v_res_773_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(
    mut v_mvarId_774_: *mut LeanObject,
    mut v_x_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
    mut v___y_777_: *mut LeanObject,
    mut v___y_778_: *mut LeanObject,
    mut v___y_779_: *mut LeanObject,
    mut v___y_780_: *mut LeanObject,
    mut v___y_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_779_);
                lean_inc_ref(v___y_778_);
                lean_inc(v___y_777_);
                lean_inc_ref(v___y_776_);
                v___f_785_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_785_, 0, v_x_775_);
                lean_closure_set(v___f_785_, 1, v___y_776_);
                lean_closure_set(v___f_785_, 2, v___y_777_);
                lean_closure_set(v___f_785_, 3, v___y_778_);
                lean_closure_set(v___f_785_, 4, v___y_779_);
                v___x_786_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_774_,
                    v___f_785_,
                    v___y_780_,
                    v___y_781_,
                    v___y_782_,
                    v___y_783_,
                );
                if lean_obj_tag(v___x_786_) == 0 {
                    return v___x_786_;
                } else {
                    v_a_787_ = lean_ctor_get(v___x_786_, 0);
                    v_isSharedCheck_794_ = (!lean_is_exclusive(v___x_786_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v___x_789_ = v___x_786_;
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_787_);
                        lean_dec(v___x_786_);
                        v___x_789_ = lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_794_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_790_ == 0 {
                    v___x_792_ = v___x_789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
                    v___x_792_ = v_reuseFailAlloc_793_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg___boxed(
    mut v_mvarId_795_: *mut LeanObject,
    mut v_x_796_: *mut LeanObject,
    mut v___y_797_: *mut LeanObject,
    mut v___y_798_: *mut LeanObject,
    mut v___y_799_: *mut LeanObject,
    mut v___y_800_: *mut LeanObject,
    mut v___y_801_: *mut LeanObject,
    mut v___y_802_: *mut LeanObject,
    mut v___y_803_: *mut LeanObject,
    mut v___y_804_: *mut LeanObject,
    mut v___y_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_806_: *mut LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_mvarId_795_, v_x_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
    lean_dec(v___y_804_);
    lean_dec_ref(v___y_803_);
    lean_dec(v___y_802_);
    lean_dec_ref(v___y_801_);
    lean_dec(v___y_800_);
    lean_dec_ref(v___y_799_);
    lean_dec(v___y_798_);
    lean_dec_ref(v___y_797_);
    return v_res_806_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4(
    mut v_00_u03b1_807_: *mut LeanObject,
    mut v_mvarId_808_: *mut LeanObject,
    mut v_x_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
    mut v___y_812_: *mut LeanObject,
    mut v___y_813_: *mut LeanObject,
    mut v___y_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
    mut v___y_816_: *mut LeanObject,
    mut v___y_817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    v___x_819_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_mvarId_808_, v_x_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
    return v___x_819_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___boxed(
    mut v_00_u03b1_820_: *mut LeanObject,
    mut v_mvarId_821_: *mut LeanObject,
    mut v_x_822_: *mut LeanObject,
    mut v___y_823_: *mut LeanObject,
    mut v___y_824_: *mut LeanObject,
    mut v___y_825_: *mut LeanObject,
    mut v___y_826_: *mut LeanObject,
    mut v___y_827_: *mut LeanObject,
    mut v___y_828_: *mut LeanObject,
    mut v___y_829_: *mut LeanObject,
    mut v___y_830_: *mut LeanObject,
    mut v___y_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_832_: *mut LeanObject = core::ptr::null_mut();
    v_res_832_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4(
            v_00_u03b1_820_,
            v_mvarId_821_,
            v_x_822_,
            v___y_823_,
            v___y_824_,
            v___y_825_,
            v___y_826_,
            v___y_827_,
            v___y_828_,
            v___y_829_,
            v___y_830_,
        );
    lean_dec(v___y_830_);
    lean_dec_ref(v___y_829_);
    lean_dec(v___y_828_);
    lean_dec_ref(v___y_827_);
    lean_dec(v___y_826_);
    lean_dec_ref(v___y_825_);
    lean_dec(v___y_824_);
    lean_dec_ref(v___y_823_);
    return v_res_832_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(
    mut v_x_833_: *mut LeanObject,
    mut v_x_834_: *mut LeanObject,
    mut v_x_835_: *mut LeanObject,
    mut v_x_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: u8 = 0;
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_837_ = lean_ctor_get(v_x_833_, 0);
                v_vs_838_ = lean_ctor_get(v_x_833_, 1);
                v_isSharedCheck_862_ = (!lean_is_exclusive(v_x_833_)) as u8;
                if v_isSharedCheck_862_ == 0 {
                    v___x_840_ = v_x_833_;
                    v_isShared_841_ = v_isSharedCheck_862_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_838_);
                    lean_inc(v_ks_837_);
                    lean_dec(v_x_833_);
                    v___x_840_ = lean_box(0);
                    v_isShared_841_ = v_isSharedCheck_862_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_842_ = lean_array_get_size(v_ks_837_);
                v___x_843_ = lean_nat_dec_lt(v_x_834_, v___x_842_);
                if v___x_843_ == 0 {
                    lean_dec(v_x_834_);
                    v___x_844_ = lean_array_push(v_ks_837_, v_x_835_);
                    v___x_845_ = lean_array_push(v_vs_838_, v_x_836_);
                    if v_isShared_841_ == 0 {
                        lean_ctor_set(v___x_840_, 1, v___x_845_);
                        lean_ctor_set(v___x_840_, 0, v___x_844_);
                        v___x_847_ = v___x_840_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_844_);
                        lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
                        v___x_847_ = v_reuseFailAlloc_848_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_849_ = lean_array_fget_borrowed(v_ks_837_, v_x_834_);
                    v___x_850_ = l_Lean_instBEqMVarId_beq(v_x_835_, v_k_x27_849_);
                    if v___x_850_ == 0 {
                        if v_isShared_841_ == 0 {
                            v___x_852_ = v___x_840_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_856_, 0, v_ks_837_);
                            lean_ctor_set(v_reuseFailAlloc_856_, 1, v_vs_838_);
                            v___x_852_ = v_reuseFailAlloc_856_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_857_ = lean_array_fset(v_ks_837_, v_x_834_, v_x_835_);
                        v___x_858_ = lean_array_fset(v_vs_838_, v_x_834_, v_x_836_);
                        lean_dec(v_x_834_);
                        if v_isShared_841_ == 0 {
                            lean_ctor_set(v___x_840_, 1, v___x_858_);
                            lean_ctor_set(v___x_840_, 0, v___x_857_);
                            v___x_860_ = v___x_840_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_857_);
                            lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_858_);
                            v___x_860_ = v_reuseFailAlloc_861_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_847_;
            }
            3 => {
                v___x_853_ = lean_unsigned_to_nat(1);
                v___x_854_ = lean_nat_add(v_x_834_, v___x_853_);
                lean_dec(v_x_834_);
                v_x_833_ = v___x_852_;
                v_x_834_ = v___x_854_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(
    mut v_n_863_: *mut LeanObject,
    mut v_k_864_: *mut LeanObject,
    mut v_v_865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v___x_866_ = lean_unsigned_to_nat(0);
    v___x_867_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_n_863_, v___x_866_, v_k_864_, v_v_865_);
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_868_: usize = 0;
    let mut v___x_869_: usize = 0;
    let mut v___x_870_: usize = 0;
    v___x_868_ = 5usize;
    v___x_869_ = 1usize;
    v___x_870_ = lean_usize_shift_left(v___x_869_, v___x_868_);
    return v___x_870_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_871_: usize = 0;
    let mut v___x_872_: usize = 0;
    let mut v___x_873_: usize = 0;
    v___x_871_ = 1usize;
    v___x_872_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__0);
    v___x_873_ = lean_usize_sub(v___x_872_, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_874_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(
    mut v_x_875_: *mut LeanObject,
    mut v_x_876_: usize,
    mut v_x_877_: usize,
    mut v_x_878_: *mut LeanObject,
    mut v_x_879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: usize = 0;
    let mut v___x_882_: usize = 0;
    let mut v___x_883_: usize = 0;
    let mut v___x_884_: usize = 0;
    let mut v_j_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: u8 = 0;
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_890_: u8 = 0;
    let mut v_v_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_904_: u8 = 0;
    let mut v___x_905_: u8 = 0;
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v_node_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_915_: u8 = 0;
    let mut v___x_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_924_: u8 = 0;
    let mut v_unused_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_930_: u8 = 0;
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_935_: u8 = 0;
    let mut v_ks_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: usize = 0;
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: u8 = 0;
    let mut v_reuseFailAlloc_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_875_) == 0 {
                    v_es_880_ = lean_ctor_get(v_x_875_, 0);
                    v___x_881_ = 5usize;
                    v___x_882_ = 1usize;
                    v___x_883_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__1);
                    v___x_884_ = lean_usize_land(v_x_876_, v___x_883_);
                    v_j_885_ = lean_usize_to_nat(v___x_884_);
                    v___x_886_ = lean_array_get_size(v_es_880_);
                    v___x_887_ = lean_nat_dec_lt(v_j_885_, v___x_886_);
                    if v___x_887_ == 0 {
                        lean_dec(v_j_885_);
                        lean_dec(v_x_879_);
                        lean_dec(v_x_878_);
                        return v_x_875_;
                    } else {
                        lean_inc_ref(v_es_880_);
                        v_isSharedCheck_924_ = (!lean_is_exclusive(v_x_875_)) as u8;
                        if v_isSharedCheck_924_ == 0 {
                            v_unused_925_ = lean_ctor_get(v_x_875_, 0);
                            lean_dec(v_unused_925_);
                            v___x_889_ = v_x_875_;
                            v_isShared_890_ = v_isSharedCheck_924_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_875_);
                            v___x_889_ = lean_box(0);
                            v_isShared_890_ = v_isSharedCheck_924_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_926_ = lean_ctor_get(v_x_875_, 0);
                    v_vs_927_ = lean_ctor_get(v_x_875_, 1);
                    v_isSharedCheck_947_ = (!lean_is_exclusive(v_x_875_)) as u8;
                    if v_isSharedCheck_947_ == 0 {
                        v___x_929_ = v_x_875_;
                        v_isShared_930_ = v_isSharedCheck_947_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_927_);
                        lean_inc(v_ks_926_);
                        lean_dec(v_x_875_);
                        v___x_929_ = lean_box(0);
                        v_isShared_930_ = v_isSharedCheck_947_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_891_ = lean_array_fget(v_es_880_, v_j_885_);
                v___x_892_ = lean_box(0);
                v_xs_x27_893_ = lean_array_fset(v_es_880_, v_j_885_, v___x_892_);
                match lean_obj_tag(v_v_891_) {
                    0 => {
                        v_key_900_ = lean_ctor_get(v_v_891_, 0);
                        v_val_901_ = lean_ctor_get(v_v_891_, 1);
                        v_isSharedCheck_911_ = (!lean_is_exclusive(v_v_891_)) as u8;
                        if v_isSharedCheck_911_ == 0 {
                            v___x_903_ = v_v_891_;
                            v_isShared_904_ = v_isSharedCheck_911_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_901_);
                            lean_inc(v_key_900_);
                            lean_dec(v_v_891_);
                            v___x_903_ = lean_box(0);
                            v_isShared_904_ = v_isSharedCheck_911_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_912_ = lean_ctor_get(v_v_891_, 0);
                        v_isSharedCheck_922_ = (!lean_is_exclusive(v_v_891_)) as u8;
                        if v_isSharedCheck_922_ == 0 {
                            v___x_914_ = v_v_891_;
                            v_isShared_915_ = v_isSharedCheck_922_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_912_);
                            lean_dec(v_v_891_);
                            v___x_914_ = lean_box(0);
                            v_isShared_915_ = v_isSharedCheck_922_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_923_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_923_, 0, v_x_878_);
                        lean_ctor_set(v___x_923_, 1, v_x_879_);
                        v___y_895_ = v___x_923_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_896_ = lean_array_fset(v_xs_x27_893_, v_j_885_, v___y_895_);
                lean_dec(v_j_885_);
                if v_isShared_890_ == 0 {
                    lean_ctor_set(v___x_889_, 0, v___x_896_);
                    v___x_898_ = v___x_889_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
                    v___x_898_ = v_reuseFailAlloc_899_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_898_;
            }
            4 => {
                v___x_905_ = l_Lean_instBEqMVarId_beq(v_x_878_, v_key_900_);
                if v___x_905_ == 0 {
                    lean_del_object(v___x_903_);
                    v___x_906_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_900_, v_val_901_, v_x_878_, v_x_879_,
                    );
                    v___x_907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_907_, 0, v___x_906_);
                    v___y_895_ = v___x_907_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_901_);
                    lean_dec(v_key_900_);
                    if v_isShared_904_ == 0 {
                        lean_ctor_set(v___x_903_, 1, v_x_879_);
                        lean_ctor_set(v___x_903_, 0, v_x_878_);
                        v___x_909_ = v___x_903_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_910_, 0, v_x_878_);
                        lean_ctor_set(v_reuseFailAlloc_910_, 1, v_x_879_);
                        v___x_909_ = v_reuseFailAlloc_910_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_895_ = v___x_909_;
                state = 2;
                continue;
            }
            6 => {
                v___x_916_ = lean_usize_shift_right(v_x_876_, v___x_881_);
                v___x_917_ = lean_usize_add(v_x_877_, v___x_882_);
                v___x_918_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_node_912_, v___x_916_, v___x_917_, v_x_878_, v_x_879_);
                if v_isShared_915_ == 0 {
                    lean_ctor_set(v___x_914_, 0, v___x_918_);
                    v___x_920_ = v___x_914_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
                    v___x_920_ = v_reuseFailAlloc_921_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_895_ = v___x_920_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_930_ == 0 {
                    v___x_932_ = v___x_929_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_946_, 0, v_ks_926_);
                    lean_ctor_set(v_reuseFailAlloc_946_, 1, v_vs_927_);
                    v___x_932_ = v_reuseFailAlloc_946_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_933_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v___x_932_, v_x_878_, v_x_879_);
                v___x_941_ = 7usize;
                v___x_942_ = lean_usize_dec_le(v___x_941_, v_x_877_);
                if v___x_942_ == 0 {
                    v___x_943_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_933_);
                    v___x_944_ = lean_unsigned_to_nat(4);
                    v___x_945_ = lean_nat_dec_lt(v___x_943_, v___x_944_);
                    lean_dec(v___x_943_);
                    v___y_935_ = v___x_945_;
                    state = 10;
                    continue;
                } else {
                    v___y_935_ = v___x_942_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_935_ == 0 {
                    v_ks_936_ = lean_ctor_get(v_newNode_933_, 0);
                    lean_inc_ref(v_ks_936_);
                    v_vs_937_ = lean_ctor_get(v_newNode_933_, 1);
                    lean_inc_ref(v_vs_937_);
                    lean_dec_ref(v_newNode_933_);
                    v___x_938_ = lean_unsigned_to_nat(0);
                    v___x_939_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___closed__2);
                    v___x_940_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_x_877_, v_ks_936_, v_vs_937_, v___x_938_, v___x_939_);
                    lean_dec_ref(v_vs_937_);
                    lean_dec_ref(v_ks_936_);
                    return v___x_940_;
                } else {
                    return v_newNode_933_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(
    mut v_depth_948_: usize,
    mut v_keys_949_: *mut LeanObject,
    mut v_vals_950_: *mut LeanObject,
    mut v_i_951_: *mut LeanObject,
    mut v_entries_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: u8 = 0;
    let mut v_k_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: u64 = 0;
    let mut v_h_958_: usize = 0;
    let mut v___x_959_: usize = 0;
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: usize = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: usize = 0;
    let mut v_h_964_: usize = 0;
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_953_ = lean_array_get_size(v_keys_949_);
                v___x_954_ = lean_nat_dec_lt(v_i_951_, v___x_953_);
                if v___x_954_ == 0 {
                    lean_dec(v_i_951_);
                    return v_entries_952_;
                } else {
                    v_k_955_ = lean_array_fget_borrowed(v_keys_949_, v_i_951_);
                    v_v_956_ = lean_array_fget_borrowed(v_vals_950_, v_i_951_);
                    v___x_957_ = l_Lean_instHashableMVarId_hash(v_k_955_);
                    v_h_958_ = lean_uint64_to_usize(v___x_957_);
                    v___x_959_ = 5usize;
                    v___x_960_ = lean_unsigned_to_nat(1);
                    v___x_961_ = 1usize;
                    v___x_962_ = lean_usize_sub(v_depth_948_, v___x_961_);
                    v___x_963_ = lean_usize_mul(v___x_959_, v___x_962_);
                    v_h_964_ = lean_usize_shift_right(v_h_958_, v___x_963_);
                    v___x_965_ = lean_nat_add(v_i_951_, v___x_960_);
                    lean_dec(v_i_951_);
                    lean_inc(v_v_956_);
                    lean_inc(v_k_955_);
                    v___x_966_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_entries_952_, v_h_964_, v_depth_948_, v_k_955_, v_v_956_);
                    v_i_951_ = v___x_965_;
                    v_entries_952_ = v___x_966_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_depth_968_: *mut LeanObject,
    mut v_keys_969_: *mut LeanObject,
    mut v_vals_970_: *mut LeanObject,
    mut v_i_971_: *mut LeanObject,
    mut v_entries_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_973_: usize = 0;
    let mut v_res_974_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_973_ = lean_unbox_usize(v_depth_968_);
    lean_dec(v_depth_968_);
    v_res_974_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_boxed_973_, v_keys_969_, v_vals_970_, v_i_971_, v_entries_972_);
    lean_dec_ref(v_vals_970_);
    lean_dec_ref(v_keys_969_);
    return v_res_974_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_x_975_: *mut LeanObject,
    mut v_x_976_: *mut LeanObject,
    mut v_x_977_: *mut LeanObject,
    mut v_x_978_: *mut LeanObject,
    mut v_x_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7047__boxed_980_: usize = 0;
    let mut v_x_7048__boxed_981_: usize = 0;
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_x_7047__boxed_980_ = lean_unbox_usize(v_x_976_);
    lean_dec(v_x_976_);
    v_x_7048__boxed_981_ = lean_unbox_usize(v_x_977_);
    lean_dec(v_x_977_);
    v_res_982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_975_, v_x_7047__boxed_980_, v_x_7048__boxed_981_, v_x_978_, v_x_979_);
    return v_res_982_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(
    mut v_x_983_: *mut LeanObject,
    mut v_x_984_: *mut LeanObject,
    mut v_x_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_986_: u64 = 0;
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: usize = 0;
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    v___x_986_ = l_Lean_instHashableMVarId_hash(v_x_984_);
    v___x_987_ = lean_uint64_to_usize(v___x_986_);
    v___x_988_ = 1usize;
    v___x_989_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_983_, v___x_987_, v___x_988_, v_x_984_, v_x_985_);
    return v___x_989_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(
    mut v_mvarId_990_: *mut LeanObject,
    mut v_val_991_: *mut LeanObject,
    mut v___y_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v_depth_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1026_: u8 = 0;
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_994_ = lean_st_ref_take(v___y_992_);
                v_mctx_995_ = lean_ctor_get(v___x_994_, 0);
                v_cache_996_ = lean_ctor_get(v___x_994_, 1);
                v_zetaDeltaFVarIds_997_ = lean_ctor_get(v___x_994_, 2);
                v_postponed_998_ = lean_ctor_get(v___x_994_, 3);
                v_diag_999_ = lean_ctor_get(v___x_994_, 4);
                v_isSharedCheck_1027_ = (!lean_is_exclusive(v___x_994_)) as u8;
                if v_isSharedCheck_1027_ == 0 {
                    v___x_1001_ = v___x_994_;
                    v_isShared_1002_ = v_isSharedCheck_1027_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_999_);
                    lean_inc(v_postponed_998_);
                    lean_inc(v_zetaDeltaFVarIds_997_);
                    lean_inc(v_cache_996_);
                    lean_inc(v_mctx_995_);
                    lean_dec(v___x_994_);
                    v___x_1001_ = lean_box(0);
                    v_isShared_1002_ = v_isSharedCheck_1027_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1003_ = lean_ctor_get(v_mctx_995_, 0);
                v_levelAssignDepth_1004_ = lean_ctor_get(v_mctx_995_, 1);
                v_lmvarCounter_1005_ = lean_ctor_get(v_mctx_995_, 2);
                v_mvarCounter_1006_ = lean_ctor_get(v_mctx_995_, 3);
                v_lDecls_1007_ = lean_ctor_get(v_mctx_995_, 4);
                v_decls_1008_ = lean_ctor_get(v_mctx_995_, 5);
                v_userNames_1009_ = lean_ctor_get(v_mctx_995_, 6);
                v_lAssignment_1010_ = lean_ctor_get(v_mctx_995_, 7);
                v_eAssignment_1011_ = lean_ctor_get(v_mctx_995_, 8);
                v_dAssignment_1012_ = lean_ctor_get(v_mctx_995_, 9);
                v_isSharedCheck_1026_ = (!lean_is_exclusive(v_mctx_995_)) as u8;
                if v_isSharedCheck_1026_ == 0 {
                    v___x_1014_ = v_mctx_995_;
                    v_isShared_1015_ = v_isSharedCheck_1026_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_1012_);
                    lean_inc(v_eAssignment_1011_);
                    lean_inc(v_lAssignment_1010_);
                    lean_inc(v_userNames_1009_);
                    lean_inc(v_decls_1008_);
                    lean_inc(v_lDecls_1007_);
                    lean_inc(v_mvarCounter_1006_);
                    lean_inc(v_lmvarCounter_1005_);
                    lean_inc(v_levelAssignDepth_1004_);
                    lean_inc(v_depth_1003_);
                    lean_dec(v_mctx_995_);
                    v___x_1014_ = lean_box(0);
                    v_isShared_1015_ = v_isSharedCheck_1026_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1016_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_eAssignment_1011_, v_mvarId_990_, v_val_991_);
                if v_isShared_1015_ == 0 {
                    lean_ctor_set(v___x_1014_, 8, v___x_1016_);
                    v___x_1018_ = v___x_1014_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_depth_1003_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_levelAssignDepth_1004_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 2, v_lmvarCounter_1005_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 3, v_mvarCounter_1006_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 4, v_lDecls_1007_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 5, v_decls_1008_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 6, v_userNames_1009_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 7, v_lAssignment_1010_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 8, v___x_1016_);
                    lean_ctor_set(v_reuseFailAlloc_1025_, 9, v_dAssignment_1012_);
                    v___x_1018_ = v_reuseFailAlloc_1025_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1002_ == 0 {
                    lean_ctor_set(v___x_1001_, 0, v___x_1018_);
                    v___x_1020_ = v___x_1001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1018_);
                    lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_cache_996_);
                    lean_ctor_set(v_reuseFailAlloc_1024_, 2, v_zetaDeltaFVarIds_997_);
                    lean_ctor_set(v_reuseFailAlloc_1024_, 3, v_postponed_998_);
                    lean_ctor_set(v_reuseFailAlloc_1024_, 4, v_diag_999_);
                    v___x_1020_ = v_reuseFailAlloc_1024_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1021_ = lean_st_ref_set(v___y_992_, v___x_1020_);
                v___x_1022_ = lean_box(0);
                v___x_1023_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1023_, 0, v___x_1022_);
                return v___x_1023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg___boxed(
    mut v_mvarId_1028_: *mut LeanObject,
    mut v_val_1029_: *mut LeanObject,
    mut v___y_1030_: *mut LeanObject,
    mut v___y_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1032_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(
            v_mvarId_1028_,
            v_val_1029_,
            v___y_1030_,
        );
    lean_dec(v___y_1030_);
    return v_res_1032_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(
    mut v_msgData_1033_: *mut LeanObject,
    mut v___y_1034_: *mut LeanObject,
    mut v___y_1035_: *mut LeanObject,
    mut v___y_1036_: *mut LeanObject,
    mut v___y_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    v___x_1039_ = lean_st_ref_get(v___y_1037_);
    v_env_1040_ = lean_ctor_get(v___x_1039_, 0);
    lean_inc_ref(v_env_1040_);
    lean_dec(v___x_1039_);
    v___x_1041_ = lean_st_ref_get(v___y_1035_);
    v_mctx_1042_ = lean_ctor_get(v___x_1041_, 0);
    lean_inc_ref(v_mctx_1042_);
    lean_dec(v___x_1041_);
    v_lctx_1043_ = lean_ctor_get(v___y_1034_, 2);
    v_options_1044_ = lean_ctor_get(v___y_1036_, 2);
    lean_inc_ref(v_options_1044_);
    lean_inc_ref(v_lctx_1043_);
    v___x_1045_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1045_, 0, v_env_1040_);
    lean_ctor_set(v___x_1045_, 1, v_mctx_1042_);
    lean_ctor_set(v___x_1045_, 2, v_lctx_1043_);
    lean_ctor_set(v___x_1045_, 3, v_options_1044_);
    v___x_1046_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1046_, 0, v___x_1045_);
    lean_ctor_set(v___x_1046_, 1, v_msgData_1033_);
    v___x_1047_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1047_, 0, v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4___boxed(
    mut v_msgData_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
    mut v___y_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1054_: *mut LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msgData_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
    lean_dec(v___y_1052_);
    lean_dec_ref(v___y_1051_);
    lean_dec(v___y_1050_);
    lean_dec_ref(v___y_1049_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(
    mut v_msg_1055_: *mut LeanObject,
    mut v___y_1056_: *mut LeanObject,
    mut v___y_1057_: *mut LeanObject,
    mut v___y_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1061_ = lean_ctor_get(v___y_1058_, 5);
                v___x_1062_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3_spec__4(v_msg_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
                v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
                v_isSharedCheck_1071_ = (!lean_is_exclusive(v___x_1062_)) as u8;
                if v_isSharedCheck_1071_ == 0 {
                    v___x_1065_ = v___x_1062_;
                    v_isShared_1066_ = v_isSharedCheck_1071_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1063_);
                    lean_dec(v___x_1062_);
                    v___x_1065_ = lean_box(0);
                    v_isShared_1066_ = v_isSharedCheck_1071_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1061_);
                v___x_1067_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1067_, 0, v_ref_1061_);
                lean_ctor_set(v___x_1067_, 1, v_a_1063_);
                if v_isShared_1066_ == 0 {
                    lean_ctor_set_tag(v___x_1065_, 1);
                    lean_ctor_set(v___x_1065_, 0, v___x_1067_);
                    v___x_1069_ = v___x_1065_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
                    v___x_1069_ = v_reuseFailAlloc_1070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1069_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg___boxed(
    mut v_msg_1072_: *mut LeanObject,
    mut v___y_1073_: *mut LeanObject,
    mut v___y_1074_: *mut LeanObject,
    mut v___y_1075_: *mut LeanObject,
    mut v___y_1076_: *mut LeanObject,
    mut v___y_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1078_: *mut LeanObject = core::ptr::null_mut();
    v_res_1078_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(
            v_msg_1072_,
            v___y_1073_,
            v___y_1074_,
            v___y_1075_,
            v___y_1076_,
        );
    lean_dec(v___y_1076_);
    lean_dec_ref(v___y_1075_);
    lean_dec(v___y_1074_);
    lean_dec_ref(v___y_1073_);
    return v_res_1078_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__5;
    v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
    return v___x_1086_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(
    mut v_a_1087_: *mut LeanObject,
    mut v_hyp_1088_: *mut LeanObject,
    mut v___x_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
    mut v___y_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
    mut v___y_1094_: *mut LeanObject,
    mut v___y_1095_: *mut LeanObject,
    mut v___y_1096_: *mut LeanObject,
    mut v___y_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_restHyps_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1136_: u8 = 0;
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v_a_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1158_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_1087_);
                v___x_1099_ = l_Lean_MVarId_getType(
                    v_a_1087_,
                    v___y_1094_,
                    v___y_1095_,
                    v___y_1096_,
                    v___y_1097_,
                );
                if lean_obj_tag(v___x_1099_) == 0 {
                    v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
                    lean_inc(v_a_1100_);
                    lean_dec_ref_known(v___x_1099_, 1);
                    v___x_1101_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__1___redArg(v_a_1100_, v___y_1095_);
                    v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
                    lean_inc(v_a_1102_);
                    lean_dec_ref(v___x_1101_);
                    v___x_1103_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1102_);
                    lean_dec(v_a_1102_);
                    if lean_obj_tag(v___x_1103_) == 1 {
                        v_val_1104_ = lean_ctor_get(v___x_1103_, 0);
                        lean_inc_n(v_val_1104_, 2);
                        lean_dec_ref_known(v___x_1103_, 1);
                        v___x_1105_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
                            v_val_1104_,
                            v_hyp_1088_,
                            v___y_1094_,
                            v___y_1095_,
                            v___y_1096_,
                            v___y_1097_,
                        );
                        if lean_obj_tag(v___x_1105_) == 0 {
                            v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
                            lean_inc(v_a_1106_);
                            lean_dec_ref_known(v___x_1105_, 1);
                            lean_inc(v_val_1104_);
                            v___x_1107_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(
                                v_a_1106_,
                                v_val_1104_,
                            );
                            v___x_1108_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1107_);
                            v___x_1109_ = lean_box(0);
                            v___x_1110_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                v___x_1108_,
                                v___x_1109_,
                                v___y_1094_,
                                v___y_1095_,
                                v___y_1096_,
                                v___y_1097_,
                            );
                            if lean_obj_tag(v___x_1110_) == 0 {
                                v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
                                lean_inc_n(v_a_1111_, 2);
                                lean_dec_ref_known(v___x_1110_, 1);
                                v_u_1112_ = lean_ctor_get(v_val_1104_, 0);
                                lean_inc(v_u_1112_);
                                v_00_u03c3s_1113_ = lean_ctor_get(v_val_1104_, 1);
                                lean_inc_ref(v_00_u03c3s_1113_);
                                v_hyps_1114_ = lean_ctor_get(v_val_1104_, 2);
                                lean_inc_ref(v_hyps_1114_);
                                v_target_1115_ = lean_ctor_get(v_val_1104_, 3);
                                lean_inc_ref(v_target_1115_);
                                lean_dec(v_val_1104_);
                                v_focusHyp_1116_ = lean_ctor_get(v_a_1106_, 0);
                                lean_inc_ref(v_focusHyp_1116_);
                                v_restHyps_1117_ = lean_ctor_get(v_a_1106_, 1);
                                lean_inc_ref(v_restHyps_1117_);
                                v_proof_1118_ = lean_ctor_get(v_a_1106_, 2);
                                lean_inc_ref(v_proof_1118_);
                                lean_dec(v_a_1106_);
                                v___x_1119_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__0;
                                v___x_1120_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__1;
                                v___x_1121_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__2;
                                v___x_1122_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__3;
                                v___x_1123_ =
                                    l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__4;
                                v___x_1124_ = l_Lean_Name_mkStr6(
                                    v___x_1119_,
                                    v___x_1120_,
                                    v___x_1121_,
                                    v___x_1089_,
                                    v___x_1122_,
                                    v___x_1123_,
                                );
                                v___x_1125_ = lean_box(0);
                                v___x_1126_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1126_, 0, v_u_1112_);
                                lean_ctor_set(v___x_1126_, 1, v___x_1125_);
                                v___x_1127_ = l_Lean_mkConst(v___x_1124_, v___x_1126_);
                                v___x_1128_ = l_Lean_mkApp7(
                                    v___x_1127_,
                                    v_00_u03c3s_1113_,
                                    v_hyps_1114_,
                                    v_restHyps_1117_,
                                    v_focusHyp_1116_,
                                    v_target_1115_,
                                    v_proof_1118_,
                                    v_a_1111_,
                                );
                                v___x_1129_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(v_a_1087_, v___x_1128_, v___y_1095_);
                                lean_dec_ref(v___x_1129_);
                                v___x_1130_ = l_Lean_Expr_mvarId_x21(v_a_1111_);
                                lean_dec(v_a_1111_);
                                v___x_1131_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1131_, 0, v___x_1130_);
                                lean_ctor_set(v___x_1131_, 1, v___x_1125_);
                                v___x_1132_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                    v___x_1131_,
                                    v___y_1091_,
                                    v___y_1094_,
                                    v___y_1095_,
                                    v___y_1096_,
                                    v___y_1097_,
                                );
                                return v___x_1132_;
                            } else {
                                lean_dec(v_a_1106_);
                                lean_dec(v_val_1104_);
                                lean_dec_ref(v___x_1089_);
                                lean_dec(v_a_1087_);
                                v_a_1133_ = lean_ctor_get(v___x_1110_, 0);
                                v_isSharedCheck_1140_ = (!lean_is_exclusive(v___x_1110_)) as u8;
                                if v_isSharedCheck_1140_ == 0 {
                                    v___x_1135_ = v___x_1110_;
                                    v_isShared_1136_ = v_isSharedCheck_1140_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1133_);
                                    lean_dec(v___x_1110_);
                                    v___x_1135_ = lean_box(0);
                                    v_isShared_1136_ = v_isSharedCheck_1140_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_1104_);
                            lean_dec_ref(v___x_1089_);
                            lean_dec(v_a_1087_);
                            v_a_1141_ = lean_ctor_get(v___x_1105_, 0);
                            v_isSharedCheck_1148_ = (!lean_is_exclusive(v___x_1105_)) as u8;
                            if v_isSharedCheck_1148_ == 0 {
                                v___x_1143_ = v___x_1105_;
                                v_isShared_1144_ = v_isSharedCheck_1148_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1141_);
                                lean_dec(v___x_1105_);
                                v___x_1143_ = lean_box(0);
                                v_isShared_1144_ = v_isSharedCheck_1148_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_1103_);
                        lean_dec_ref(v___x_1089_);
                        lean_dec(v_hyp_1088_);
                        lean_dec(v_a_1087_);
                        v___x_1149_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___closed__6);
                        v___x_1150_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(v___x_1149_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
                        return v___x_1150_;
                    }
                } else {
                    lean_dec_ref(v___x_1089_);
                    lean_dec(v_hyp_1088_);
                    lean_dec(v_a_1087_);
                    v_a_1151_ = lean_ctor_get(v___x_1099_, 0);
                    v_isSharedCheck_1158_ = (!lean_is_exclusive(v___x_1099_)) as u8;
                    if v_isSharedCheck_1158_ == 0 {
                        v___x_1153_ = v___x_1099_;
                        v_isShared_1154_ = v_isSharedCheck_1158_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1151_);
                        lean_dec(v___x_1099_);
                        v___x_1153_ = lean_box(0);
                        v_isShared_1154_ = v_isSharedCheck_1158_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1136_ == 0 {
                    v___x_1138_ = v___x_1135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
                    v___x_1138_ = v_reuseFailAlloc_1139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1138_;
            }
            3 => {
                if v_isShared_1144_ == 0 {
                    v___x_1146_ = v___x_1143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
                    v___x_1146_ = v_reuseFailAlloc_1147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1146_;
            }
            5 => {
                if v_isShared_1154_ == 0 {
                    v___x_1156_ = v___x_1153_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
                    v___x_1156_ = v_reuseFailAlloc_1157_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed(
    mut v_a_1159_: *mut LeanObject,
    mut v_hyp_1160_: *mut LeanObject,
    mut v___x_1161_: *mut LeanObject,
    mut v___y_1162_: *mut LeanObject,
    mut v___y_1163_: *mut LeanObject,
    mut v___y_1164_: *mut LeanObject,
    mut v___y_1165_: *mut LeanObject,
    mut v___y_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
    mut v___y_1168_: *mut LeanObject,
    mut v___y_1169_: *mut LeanObject,
    mut v___y_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1171_: *mut LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0(
        v_a_1159_,
        v_hyp_1160_,
        v___x_1161_,
        v___y_1162_,
        v___y_1163_,
        v___y_1164_,
        v___y_1165_,
        v___y_1166_,
        v___y_1167_,
        v___y_1168_,
        v___y_1169_,
    );
    lean_dec(v___y_1169_);
    lean_dec_ref(v___y_1168_);
    lean_dec(v___y_1167_);
    lean_dec_ref(v___y_1166_);
    lean_dec(v___y_1165_);
    lean_dec_ref(v___y_1164_);
    lean_dec(v___y_1163_);
    lean_dec_ref(v___y_1162_);
    return v_res_1171_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(
    mut v_x_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
    mut v_a_1190_: *mut LeanObject,
    mut v_a_1191_: *mut LeanObject,
    mut v_a_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u8 = 0;
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyp_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1194_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__2;
                v___x_1195_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4;
                lean_inc(v_x_1184_);
                v___x_1196_ = l_Lean_Syntax_isOfKind(v_x_1184_, v___x_1195_);
                if v___x_1196_ == 0 {
                    lean_dec(v_x_1184_);
                    v___x_1197_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
                    return v___x_1197_;
                } else {
                    v___x_1198_ = lean_unsigned_to_nat(1);
                    v_hyp_1199_ = l_Lean_Syntax_getArg(v_x_1184_, v___x_1198_);
                    lean_dec(v_x_1184_);
                    v___x_1200_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__6;
                    lean_inc(v_hyp_1199_);
                    v___x_1201_ = l_Lean_Syntax_isOfKind(v_hyp_1199_, v___x_1200_);
                    if v___x_1201_ == 0 {
                        lean_dec(v_hyp_1199_);
                        v___x_1202_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__0___redArg();
                        return v___x_1202_;
                    } else {
                        v___x_1203_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                            v_a_1186_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_,
                        );
                        if lean_obj_tag(v___x_1203_) == 0 {
                            v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
                            lean_inc_n(v_a_1204_, 2);
                            lean_dec_ref_known(v___x_1203_, 1);
                            v___f_1205_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                12,
                                3,
                            );
                            lean_closure_set(v___f_1205_, 0, v_a_1204_);
                            lean_closure_set(v___f_1205_, 1, v_hyp_1199_);
                            lean_closure_set(v___f_1205_, 2, v___x_1194_);
                            v___x_1206_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__4___redArg(v_a_1204_, v___f_1205_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_);
                            return v___x_1206_;
                        } else {
                            lean_dec(v_hyp_1199_);
                            v_a_1207_ = lean_ctor_get(v___x_1203_, 0);
                            v_isSharedCheck_1214_ = (!lean_is_exclusive(v___x_1203_)) as u8;
                            if v_isSharedCheck_1214_ == 0 {
                                v___x_1209_ = v___x_1203_;
                                v_isShared_1210_ = v_isSharedCheck_1214_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1207_);
                                lean_dec(v___x_1203_);
                                v___x_1209_ = lean_box(0);
                                v_isShared_1210_ = v_isSharedCheck_1214_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1210_ == 0 {
                    v___x_1212_ = v___x_1209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed(
    mut v_x_1215_: *mut LeanObject,
    mut v_a_1216_: *mut LeanObject,
    mut v_a_1217_: *mut LeanObject,
    mut v_a_1218_: *mut LeanObject,
    mut v_a_1219_: *mut LeanObject,
    mut v_a_1220_: *mut LeanObject,
    mut v_a_1221_: *mut LeanObject,
    mut v_a_1222_: *mut LeanObject,
    mut v_a_1223_: *mut LeanObject,
    mut v_a_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1225_: *mut LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear(
        v_x_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_,
        v_a_1223_,
    );
    lean_dec(v_a_1223_);
    lean_dec_ref(v_a_1222_);
    lean_dec(v_a_1221_);
    lean_dec_ref(v_a_1220_);
    lean_dec(v_a_1219_);
    lean_dec_ref(v_a_1218_);
    lean_dec(v_a_1217_);
    lean_dec_ref(v_a_1216_);
    return v_res_1225_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(
    mut v_mvarId_1226_: *mut LeanObject,
    mut v_val_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
    mut v___y_1232_: *mut LeanObject,
    mut v___y_1233_: *mut LeanObject,
    mut v___y_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    v___x_1237_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___redArg(
            v_mvarId_1226_,
            v_val_1227_,
            v___y_1233_,
        );
    return v___x_1237_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2___boxed(
    mut v_mvarId_1238_: *mut LeanObject,
    mut v_val_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
    mut v___y_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1249_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2(
        v_mvarId_1238_,
        v_val_1239_,
        v___y_1240_,
        v___y_1241_,
        v___y_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
        v___y_1246_,
        v___y_1247_,
    );
    lean_dec(v___y_1247_);
    lean_dec_ref(v___y_1246_);
    lean_dec(v___y_1245_);
    lean_dec_ref(v___y_1244_);
    lean_dec(v___y_1243_);
    lean_dec_ref(v___y_1242_);
    lean_dec(v___y_1241_);
    lean_dec_ref(v___y_1240_);
    return v_res_1249_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(
    mut v_00_u03b1_1250_: *mut LeanObject,
    mut v_msg_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    v___x_1261_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___redArg(
            v_msg_1251_,
            v___y_1256_,
            v___y_1257_,
            v___y_1258_,
            v___y_1259_,
        );
    return v___x_1261_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3___boxed(
    mut v_00_u03b1_1262_: *mut LeanObject,
    mut v_msg_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
    mut v___y_1268_: *mut LeanObject,
    mut v___y_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1273_: *mut LeanObject = core::ptr::null_mut();
    v_res_1273_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__3(
        v_00_u03b1_1262_,
        v_msg_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
        v___y_1267_,
        v___y_1268_,
        v___y_1269_,
        v___y_1270_,
        v___y_1271_,
    );
    lean_dec(v___y_1271_);
    lean_dec_ref(v___y_1270_);
    lean_dec(v___y_1269_);
    lean_dec_ref(v___y_1268_);
    lean_dec(v___y_1267_);
    lean_dec_ref(v___y_1266_);
    lean_dec(v___y_1265_);
    lean_dec_ref(v___y_1264_);
    return v_res_1273_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2(
    mut v_00_u03b2_1274_: *mut LeanObject,
    mut v_x_1275_: *mut LeanObject,
    mut v_x_1276_: *mut LeanObject,
    mut v_x_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2___redArg(v_x_1275_, v_x_1276_, v_x_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(
    mut v_00_u03b2_1279_: *mut LeanObject,
    mut v_x_1280_: *mut LeanObject,
    mut v_x_1281_: usize,
    mut v_x_1282_: usize,
    mut v_x_1283_: *mut LeanObject,
    mut v_x_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___redArg(v_x_1280_, v_x_1281_, v_x_1282_, v_x_1283_, v_x_1284_);
    return v___x_1285_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_1286_: *mut LeanObject,
    mut v_x_1287_: *mut LeanObject,
    mut v_x_1288_: *mut LeanObject,
    mut v_x_1289_: *mut LeanObject,
    mut v_x_1290_: *mut LeanObject,
    mut v_x_1291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7642__boxed_1292_: usize = 0;
    let mut v_x_7643__boxed_1293_: usize = 0;
    let mut v_res_1294_: *mut LeanObject = core::ptr::null_mut();
    v_x_7642__boxed_1292_ = lean_unbox_usize(v_x_1288_);
    lean_dec(v_x_1288_);
    v_x_7643__boxed_1293_ = lean_unbox_usize(v_x_1289_);
    lean_dec(v_x_1289_);
    v_res_1294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4(v_00_u03b2_1286_, v_x_1287_, v_x_7642__boxed_1292_, v_x_7643__boxed_1293_, v_x_1290_, v_x_1291_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7(
    mut v_00_u03b2_1295_: *mut LeanObject,
    mut v_n_1296_: *mut LeanObject,
    mut v_k_1297_: *mut LeanObject,
    mut v_v_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v___x_1299_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7___redArg(v_n_1296_, v_k_1297_, v_v_1298_);
    return v___x_1299_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(
    mut v_00_u03b2_1300_: *mut LeanObject,
    mut v_depth_1301_: usize,
    mut v_keys_1302_: *mut LeanObject,
    mut v_vals_1303_: *mut LeanObject,
    mut v_heq_1304_: *mut LeanObject,
    mut v_i_1305_: *mut LeanObject,
    mut v_entries_1306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___redArg(v_depth_1301_, v_keys_1302_, v_vals_1303_, v_i_1305_, v_entries_1306_);
    return v___x_1307_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_1308_: *mut LeanObject,
    mut v_depth_1309_: *mut LeanObject,
    mut v_keys_1310_: *mut LeanObject,
    mut v_vals_1311_: *mut LeanObject,
    mut v_heq_1312_: *mut LeanObject,
    mut v_i_1313_: *mut LeanObject,
    mut v_entries_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1315_: usize = 0;
    let mut v_res_1316_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1315_ = lean_unbox_usize(v_depth_1309_);
    lean_dec(v_depth_1309_);
    v_res_1316_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__8(v_00_u03b2_1308_, v_depth_boxed_1315_, v_keys_1310_, v_vals_1311_, v_heq_1312_, v_i_1313_, v_entries_1314_);
    lean_dec_ref(v_vals_1311_);
    lean_dec_ref(v_keys_1310_);
    return v_res_1316_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8(
    mut v_00_u03b2_1317_: *mut LeanObject,
    mut v_x_1318_: *mut LeanObject,
    mut v_x_1319_: *mut LeanObject,
    mut v_x_1320_: *mut LeanObject,
    mut v_x_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMClear_spec__2_spec__2_spec__4_spec__7_spec__8___redArg(v_x_1318_, v_x_1319_, v_x_1320_, v_x_1321_);
    return v___x_1322_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1()
-> *mut LeanObject {
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    v___x_1334_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1335_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___closed__4;
    v___x_1336_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___closed__3;
    v___x_1337_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMClear___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1338_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1334_,
        v___x_1335_,
        v___x_1336_,
        v___x_1337_,
    );
    return v___x_1338_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1___boxed(
    mut v_a_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1340_: *mut LeanObject = core::ptr::null_mut();
    v_res_1340_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
    return v_res_1340_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Clear_0__Lean_Elab_Tactic_Do_ProofMode_elabMClear___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMClear__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Clear(builtin);
}
