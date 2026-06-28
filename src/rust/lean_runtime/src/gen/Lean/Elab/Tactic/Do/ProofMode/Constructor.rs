// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Constructor
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr4, l_Lean_Name_mkStr6};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_mkApp6, l_Lean_mkConst,
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
    lean_nat_dec_lt, lean_string_dec_eq,
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
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0_value: LeanStringObject<
    24,
> = LeanStringObject {
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
        116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 83, 80, 114, 101, 100,
        46, 97, 110, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value: LeanStringObject<4> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value: LeanStringObject<3> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value: LeanStringObject<6> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5_value: LeanStringObject<4> =
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value: LeanStringObject<
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
    m_data: [97, 110, 100, 95, 105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value)
                as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value)
                as *mut LeanObject,
            7300584325018775040 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value)
                as *mut LeanObject,
            13332341187416043682 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value)
                as *mut LeanObject,
            8506583206358682360 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8_value: LeanStringObject<
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value) as *mut LeanObject,15307255260373031539 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 108, 97, 98, 77, 67, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value) as *mut LeanObject,12918838808455169038 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value) as *mut LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(
    mut v_e_702_: *mut LeanObject,
    mut v___y_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_705_: u8 = 0;
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_719_: u8 = 0;
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_unused_726_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_705_ = l_Lean_Expr_hasMVar(v_e_702_);
                if v___x_705_ == 0 {
                    v___x_706_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_706_, 0, v_e_702_);
                    return v___x_706_;
                } else {
                    v___x_707_ = lean_st_ref_get(v___y_703_);
                    v_mctx_708_ = lean_ctor_get(v___x_707_, 0);
                    lean_inc_ref(v_mctx_708_);
                    lean_dec(v___x_707_);
                    v___x_709_ = l_Lean_instantiateMVarsCore(v_mctx_708_, v_e_702_);
                    v_fst_710_ = lean_ctor_get(v___x_709_, 0);
                    lean_inc(v_fst_710_);
                    v_snd_711_ = lean_ctor_get(v___x_709_, 1);
                    lean_inc(v_snd_711_);
                    lean_dec_ref(v___x_709_);
                    v___x_712_ = lean_st_ref_take(v___y_703_);
                    v_cache_713_ = lean_ctor_get(v___x_712_, 1);
                    v_zetaDeltaFVarIds_714_ = lean_ctor_get(v___x_712_, 2);
                    v_postponed_715_ = lean_ctor_get(v___x_712_, 3);
                    v_diag_716_ = lean_ctor_get(v___x_712_, 4);
                    v_isSharedCheck_725_ = (!lean_is_exclusive(v___x_712_)) as u8;
                    if v_isSharedCheck_725_ == 0 {
                        v_unused_726_ = lean_ctor_get(v___x_712_, 0);
                        lean_dec(v_unused_726_);
                        v___x_718_ = v___x_712_;
                        v_isShared_719_ = v_isSharedCheck_725_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_716_);
                        lean_inc(v_postponed_715_);
                        lean_inc(v_zetaDeltaFVarIds_714_);
                        lean_inc(v_cache_713_);
                        lean_dec(v___x_712_);
                        v___x_718_ = lean_box(0);
                        v_isShared_719_ = v_isSharedCheck_725_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_719_ == 0 {
                    lean_ctor_set(v___x_718_, 0, v_snd_711_);
                    v___x_721_ = v___x_718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_724_, 0, v_snd_711_);
                    lean_ctor_set(v_reuseFailAlloc_724_, 1, v_cache_713_);
                    lean_ctor_set(v_reuseFailAlloc_724_, 2, v_zetaDeltaFVarIds_714_);
                    lean_ctor_set(v_reuseFailAlloc_724_, 3, v_postponed_715_);
                    lean_ctor_set(v_reuseFailAlloc_724_, 4, v_diag_716_);
                    v___x_721_ = v_reuseFailAlloc_724_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_722_ = lean_st_ref_set(v___y_703_, v___x_721_);
                v___x_723_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_723_, 0, v_fst_710_);
                return v___x_723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg___boxed(
    mut v_e_727_: *mut LeanObject,
    mut v___y_728_: *mut LeanObject,
    mut v___y_729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_730_: *mut LeanObject = core::ptr::null_mut();
    v_res_730_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_727_, v___y_728_);
    lean_dec(v___y_728_);
    return v_res_730_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(
    mut v_e_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_731_, v___y_733_);
    return v___x_737_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___boxed(
    mut v_e_738_: *mut LeanObject,
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
    mut v___y_741_: *mut LeanObject,
    mut v___y_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_744_: *mut LeanObject = core::ptr::null_mut();
    v_res_744_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(
            v_e_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_,
        );
    lean_dec(v___y_742_);
    lean_dec_ref(v___y_741_);
    lean_dec(v___y_740_);
    lean_dec_ref(v___y_739_);
    return v_res_744_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(
    mut v_msgData_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v___x_751_ = lean_st_ref_get(v___y_749_);
    v_env_752_ = lean_ctor_get(v___x_751_, 0);
    lean_inc_ref(v_env_752_);
    lean_dec(v___x_751_);
    v___x_753_ = lean_st_ref_get(v___y_747_);
    v_mctx_754_ = lean_ctor_get(v___x_753_, 0);
    lean_inc_ref(v_mctx_754_);
    lean_dec(v___x_753_);
    v_lctx_755_ = lean_ctor_get(v___y_746_, 2);
    v_options_756_ = lean_ctor_get(v___y_748_, 2);
    lean_inc_ref(v_options_756_);
    lean_inc_ref(v_lctx_755_);
    v___x_757_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_757_, 0, v_env_752_);
    lean_ctor_set(v___x_757_, 1, v_mctx_754_);
    lean_ctor_set(v___x_757_, 2, v_lctx_755_);
    lean_ctor_set(v___x_757_, 3, v_options_756_);
    v___x_758_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_758_, 0, v___x_757_);
    lean_ctor_set(v___x_758_, 1, v_msgData_745_);
    v___x_759_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_759_, 0, v___x_758_);
    return v___x_759_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0___boxed(
    mut v_msgData_760_: *mut LeanObject,
    mut v___y_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_766_: *mut LeanObject = core::ptr::null_mut();
    v_res_766_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msgData_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
    lean_dec(v___y_764_);
    lean_dec_ref(v___y_763_);
    lean_dec(v___y_762_);
    lean_dec_ref(v___y_761_);
    return v_res_766_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(
    mut v_msg_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_778_: u8 = 0;
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_783_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_773_ = lean_ctor_get(v___y_770_, 5);
                v___x_774_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msg_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
                v_a_775_ = lean_ctor_get(v___x_774_, 0);
                v_isSharedCheck_783_ = (!lean_is_exclusive(v___x_774_)) as u8;
                if v_isSharedCheck_783_ == 0 {
                    v___x_777_ = v___x_774_;
                    v_isShared_778_ = v_isSharedCheck_783_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_775_);
                    lean_dec(v___x_774_);
                    v___x_777_ = lean_box(0);
                    v_isShared_778_ = v_isSharedCheck_783_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_773_);
                v___x_779_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_779_, 0, v_ref_773_);
                lean_ctor_set(v___x_779_, 1, v_a_775_);
                if v_isShared_778_ == 0 {
                    lean_ctor_set_tag(v___x_777_, 1);
                    lean_ctor_set(v___x_777_, 0, v___x_779_);
                    v___x_781_ = v___x_777_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                    v___x_781_ = v_reuseFailAlloc_782_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg___boxed(
    mut v_msg_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
    mut v___y_786_: *mut LeanObject,
    mut v___y_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
    mut v___y_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(
            v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_,
        );
    lean_dec(v___y_788_);
    lean_dec_ref(v___y_787_);
    lean_dec(v___y_786_);
    lean_dec_ref(v___y_785_);
    return v_res_790_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(
    mut v_x_791_: *mut LeanObject,
    mut v_x_792_: *mut LeanObject,
    mut v_x_793_: *mut LeanObject,
    mut v_x_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_820_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_795_ = lean_ctor_get(v_x_791_, 0);
                v_vs_796_ = lean_ctor_get(v_x_791_, 1);
                v_isSharedCheck_820_ = (!lean_is_exclusive(v_x_791_)) as u8;
                if v_isSharedCheck_820_ == 0 {
                    v___x_798_ = v_x_791_;
                    v_isShared_799_ = v_isSharedCheck_820_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_796_);
                    lean_inc(v_ks_795_);
                    lean_dec(v_x_791_);
                    v___x_798_ = lean_box(0);
                    v_isShared_799_ = v_isSharedCheck_820_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_800_ = lean_array_get_size(v_ks_795_);
                v___x_801_ = lean_nat_dec_lt(v_x_792_, v___x_800_);
                if v___x_801_ == 0 {
                    lean_dec(v_x_792_);
                    v___x_802_ = lean_array_push(v_ks_795_, v_x_793_);
                    v___x_803_ = lean_array_push(v_vs_796_, v_x_794_);
                    if v_isShared_799_ == 0 {
                        lean_ctor_set(v___x_798_, 1, v___x_803_);
                        lean_ctor_set(v___x_798_, 0, v___x_802_);
                        v___x_805_ = v___x_798_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_802_);
                        lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_803_);
                        v___x_805_ = v_reuseFailAlloc_806_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_807_ = lean_array_fget_borrowed(v_ks_795_, v_x_792_);
                    v___x_808_ = l_Lean_instBEqMVarId_beq(v_x_793_, v_k_x27_807_);
                    if v___x_808_ == 0 {
                        if v_isShared_799_ == 0 {
                            v___x_810_ = v___x_798_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_814_, 0, v_ks_795_);
                            lean_ctor_set(v_reuseFailAlloc_814_, 1, v_vs_796_);
                            v___x_810_ = v_reuseFailAlloc_814_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_815_ = lean_array_fset(v_ks_795_, v_x_792_, v_x_793_);
                        v___x_816_ = lean_array_fset(v_vs_796_, v_x_792_, v_x_794_);
                        lean_dec(v_x_792_);
                        if v_isShared_799_ == 0 {
                            lean_ctor_set(v___x_798_, 1, v___x_816_);
                            lean_ctor_set(v___x_798_, 0, v___x_815_);
                            v___x_818_ = v___x_798_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_815_);
                            lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_816_);
                            v___x_818_ = v_reuseFailAlloc_819_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_805_;
            }
            3 => {
                v___x_811_ = lean_unsigned_to_nat(1);
                v___x_812_ = lean_nat_add(v_x_792_, v___x_811_);
                lean_dec(v_x_792_);
                v_x_791_ = v___x_810_;
                v_x_792_ = v___x_812_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_818_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_n_821_: *mut LeanObject,
    mut v_k_822_: *mut LeanObject,
    mut v_v_823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = lean_unsigned_to_nat(0);
    v___x_825_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_821_, v___x_824_, v_k_822_, v_v_823_);
    return v___x_825_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_826_: usize = 0;
    let mut v___x_827_: usize = 0;
    let mut v___x_828_: usize = 0;
    v___x_826_ = 5usize;
    v___x_827_ = 1usize;
    v___x_828_ = lean_usize_shift_left(v___x_827_, v___x_826_);
    return v___x_828_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_829_: usize = 0;
    let mut v___x_830_: usize = 0;
    let mut v___x_831_: usize = 0;
    v___x_829_ = 1usize;
    v___x_830_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_831_ = lean_usize_sub(v___x_830_, v___x_829_);
    return v___x_831_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_832_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(
    mut v_x_833_: *mut LeanObject,
    mut v_x_834_: usize,
    mut v_x_835_: usize,
    mut v_x_836_: *mut LeanObject,
    mut v_x_837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: usize = 0;
    let mut v___x_840_: usize = 0;
    let mut v___x_841_: usize = 0;
    let mut v___x_842_: usize = 0;
    let mut v_j_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: u8 = 0;
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_848_: u8 = 0;
    let mut v_v_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_869_: u8 = 0;
    let mut v_node_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_873_: u8 = 0;
    let mut v___x_874_: usize = 0;
    let mut v___x_875_: usize = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut v_unused_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_893_: u8 = 0;
    let mut v_ks_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: usize = 0;
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v_reuseFailAlloc_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_833_) == 0 {
                    v_es_838_ = lean_ctor_get(v_x_833_, 0);
                    v___x_839_ = 5usize;
                    v___x_840_ = 1usize;
                    v___x_841_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_842_ = lean_usize_land(v_x_834_, v___x_841_);
                    v_j_843_ = lean_usize_to_nat(v___x_842_);
                    v___x_844_ = lean_array_get_size(v_es_838_);
                    v___x_845_ = lean_nat_dec_lt(v_j_843_, v___x_844_);
                    if v___x_845_ == 0 {
                        lean_dec(v_j_843_);
                        lean_dec(v_x_837_);
                        lean_dec(v_x_836_);
                        return v_x_833_;
                    } else {
                        lean_inc_ref(v_es_838_);
                        v_isSharedCheck_882_ = (!lean_is_exclusive(v_x_833_)) as u8;
                        if v_isSharedCheck_882_ == 0 {
                            v_unused_883_ = lean_ctor_get(v_x_833_, 0);
                            lean_dec(v_unused_883_);
                            v___x_847_ = v_x_833_;
                            v_isShared_848_ = v_isSharedCheck_882_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_833_);
                            v___x_847_ = lean_box(0);
                            v_isShared_848_ = v_isSharedCheck_882_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_884_ = lean_ctor_get(v_x_833_, 0);
                    v_vs_885_ = lean_ctor_get(v_x_833_, 1);
                    v_isSharedCheck_905_ = (!lean_is_exclusive(v_x_833_)) as u8;
                    if v_isSharedCheck_905_ == 0 {
                        v___x_887_ = v_x_833_;
                        v_isShared_888_ = v_isSharedCheck_905_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_885_);
                        lean_inc(v_ks_884_);
                        lean_dec(v_x_833_);
                        v___x_887_ = lean_box(0);
                        v_isShared_888_ = v_isSharedCheck_905_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_849_ = lean_array_fget(v_es_838_, v_j_843_);
                v___x_850_ = lean_box(0);
                v_xs_x27_851_ = lean_array_fset(v_es_838_, v_j_843_, v___x_850_);
                match lean_obj_tag(v_v_849_) {
                    0 => {
                        v_key_858_ = lean_ctor_get(v_v_849_, 0);
                        v_val_859_ = lean_ctor_get(v_v_849_, 1);
                        v_isSharedCheck_869_ = (!lean_is_exclusive(v_v_849_)) as u8;
                        if v_isSharedCheck_869_ == 0 {
                            v___x_861_ = v_v_849_;
                            v_isShared_862_ = v_isSharedCheck_869_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_859_);
                            lean_inc(v_key_858_);
                            lean_dec(v_v_849_);
                            v___x_861_ = lean_box(0);
                            v_isShared_862_ = v_isSharedCheck_869_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_870_ = lean_ctor_get(v_v_849_, 0);
                        v_isSharedCheck_880_ = (!lean_is_exclusive(v_v_849_)) as u8;
                        if v_isSharedCheck_880_ == 0 {
                            v___x_872_ = v_v_849_;
                            v_isShared_873_ = v_isSharedCheck_880_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_870_);
                            lean_dec(v_v_849_);
                            v___x_872_ = lean_box(0);
                            v_isShared_873_ = v_isSharedCheck_880_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_881_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_881_, 0, v_x_836_);
                        lean_ctor_set(v___x_881_, 1, v_x_837_);
                        v___y_853_ = v___x_881_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_854_ = lean_array_fset(v_xs_x27_851_, v_j_843_, v___y_853_);
                lean_dec(v_j_843_);
                if v_isShared_848_ == 0 {
                    lean_ctor_set(v___x_847_, 0, v___x_854_);
                    v___x_856_ = v___x_847_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
                    v___x_856_ = v_reuseFailAlloc_857_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_856_;
            }
            4 => {
                v___x_863_ = l_Lean_instBEqMVarId_beq(v_x_836_, v_key_858_);
                if v___x_863_ == 0 {
                    lean_del_object(v___x_861_);
                    v___x_864_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_858_, v_val_859_, v_x_836_, v_x_837_,
                    );
                    v___x_865_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_865_, 0, v___x_864_);
                    v___y_853_ = v___x_865_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_859_);
                    lean_dec(v_key_858_);
                    if v_isShared_862_ == 0 {
                        lean_ctor_set(v___x_861_, 1, v_x_837_);
                        lean_ctor_set(v___x_861_, 0, v_x_836_);
                        v___x_867_ = v___x_861_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_868_, 0, v_x_836_);
                        lean_ctor_set(v_reuseFailAlloc_868_, 1, v_x_837_);
                        v___x_867_ = v_reuseFailAlloc_868_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_853_ = v___x_867_;
                state = 2;
                continue;
            }
            6 => {
                v___x_874_ = lean_usize_shift_right(v_x_834_, v___x_839_);
                v___x_875_ = lean_usize_add(v_x_835_, v___x_840_);
                v___x_876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_node_870_, v___x_874_, v___x_875_, v_x_836_, v_x_837_);
                if v_isShared_873_ == 0 {
                    lean_ctor_set(v___x_872_, 0, v___x_876_);
                    v___x_878_ = v___x_872_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
                    v___x_878_ = v_reuseFailAlloc_879_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_853_ = v___x_878_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_888_ == 0 {
                    v___x_890_ = v___x_887_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_904_, 0, v_ks_884_);
                    lean_ctor_set(v_reuseFailAlloc_904_, 1, v_vs_885_);
                    v___x_890_ = v_reuseFailAlloc_904_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_891_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_890_, v_x_836_, v_x_837_);
                v___x_899_ = 7usize;
                v___x_900_ = lean_usize_dec_le(v___x_899_, v_x_835_);
                if v___x_900_ == 0 {
                    v___x_901_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_891_);
                    v___x_902_ = lean_unsigned_to_nat(4);
                    v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
                    lean_dec(v___x_901_);
                    v___y_893_ = v___x_903_;
                    state = 10;
                    continue;
                } else {
                    v___y_893_ = v___x_900_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_893_ == 0 {
                    v_ks_894_ = lean_ctor_get(v_newNode_891_, 0);
                    lean_inc_ref(v_ks_894_);
                    v_vs_895_ = lean_ctor_get(v_newNode_891_, 1);
                    lean_inc_ref(v_vs_895_);
                    lean_dec_ref(v_newNode_891_);
                    v___x_896_ = lean_unsigned_to_nat(0);
                    v___x_897_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2);
                    v___x_898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_835_, v_ks_894_, v_vs_895_, v___x_896_, v___x_897_);
                    lean_dec_ref(v_vs_895_);
                    lean_dec_ref(v_ks_894_);
                    return v___x_898_;
                } else {
                    return v_newNode_891_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_depth_906_: usize,
    mut v_keys_907_: *mut LeanObject,
    mut v_vals_908_: *mut LeanObject,
    mut v_i_909_: *mut LeanObject,
    mut v_entries_910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: u8 = 0;
    let mut v_k_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u64 = 0;
    let mut v_h_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: usize = 0;
    let mut v___x_920_: usize = 0;
    let mut v___x_921_: usize = 0;
    let mut v_h_922_: usize = 0;
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_911_ = lean_array_get_size(v_keys_907_);
                v___x_912_ = lean_nat_dec_lt(v_i_909_, v___x_911_);
                if v___x_912_ == 0 {
                    lean_dec(v_i_909_);
                    return v_entries_910_;
                } else {
                    v_k_913_ = lean_array_fget_borrowed(v_keys_907_, v_i_909_);
                    v_v_914_ = lean_array_fget_borrowed(v_vals_908_, v_i_909_);
                    v___x_915_ = l_Lean_instHashableMVarId_hash(v_k_913_);
                    v_h_916_ = lean_uint64_to_usize(v___x_915_);
                    v___x_917_ = 5usize;
                    v___x_918_ = lean_unsigned_to_nat(1);
                    v___x_919_ = 1usize;
                    v___x_920_ = lean_usize_sub(v_depth_906_, v___x_919_);
                    v___x_921_ = lean_usize_mul(v___x_917_, v___x_920_);
                    v_h_922_ = lean_usize_shift_right(v_h_916_, v___x_921_);
                    v___x_923_ = lean_nat_add(v_i_909_, v___x_918_);
                    lean_dec(v_i_909_);
                    lean_inc(v_v_914_);
                    lean_inc(v_k_913_);
                    v___x_924_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_entries_910_, v_h_922_, v_depth_906_, v_k_913_, v_v_914_);
                    v_i_909_ = v___x_923_;
                    v_entries_910_ = v___x_924_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_depth_926_: *mut LeanObject,
    mut v_keys_927_: *mut LeanObject,
    mut v_vals_928_: *mut LeanObject,
    mut v_i_929_: *mut LeanObject,
    mut v_entries_930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_931_: usize = 0;
    let mut v_res_932_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_931_ = lean_unbox_usize(v_depth_926_);
    lean_dec(v_depth_926_);
    v_res_932_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_931_, v_keys_927_, v_vals_928_, v_i_929_, v_entries_930_);
    lean_dec_ref(v_vals_928_);
    lean_dec_ref(v_keys_927_);
    return v_res_932_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_x_933_: *mut LeanObject,
    mut v_x_934_: *mut LeanObject,
    mut v_x_935_: *mut LeanObject,
    mut v_x_936_: *mut LeanObject,
    mut v_x_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_3583__boxed_938_: usize = 0;
    let mut v_x_3584__boxed_939_: usize = 0;
    let mut v_res_940_: *mut LeanObject = core::ptr::null_mut();
    v_x_3583__boxed_938_ = lean_unbox_usize(v_x_934_);
    lean_dec(v_x_934_);
    v_x_3584__boxed_939_ = lean_unbox_usize(v_x_935_);
    lean_dec(v_x_935_);
    v_res_940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_933_, v_x_3583__boxed_938_, v_x_3584__boxed_939_, v_x_936_, v_x_937_);
    return v_res_940_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(
    mut v_x_941_: *mut LeanObject,
    mut v_x_942_: *mut LeanObject,
    mut v_x_943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_944_: u64 = 0;
    let mut v___x_945_: usize = 0;
    let mut v___x_946_: usize = 0;
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    v___x_944_ = l_Lean_instHashableMVarId_hash(v_x_942_);
    v___x_945_ = lean_uint64_to_usize(v___x_944_);
    v___x_946_ = 1usize;
    v___x_947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_941_, v___x_945_, v___x_946_, v_x_942_, v_x_943_);
    return v___x_947_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(
    mut v_mvarId_948_: *mut LeanObject,
    mut v_val_949_: *mut LeanObject,
    mut v___y_950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_960_: u8 = 0;
    let mut v_depth_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_973_: u8 = 0;
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_984_: u8 = 0;
    let mut v_isSharedCheck_985_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_952_ = lean_st_ref_take(v___y_950_);
                v_mctx_953_ = lean_ctor_get(v___x_952_, 0);
                v_cache_954_ = lean_ctor_get(v___x_952_, 1);
                v_zetaDeltaFVarIds_955_ = lean_ctor_get(v___x_952_, 2);
                v_postponed_956_ = lean_ctor_get(v___x_952_, 3);
                v_diag_957_ = lean_ctor_get(v___x_952_, 4);
                v_isSharedCheck_985_ = (!lean_is_exclusive(v___x_952_)) as u8;
                if v_isSharedCheck_985_ == 0 {
                    v___x_959_ = v___x_952_;
                    v_isShared_960_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_957_);
                    lean_inc(v_postponed_956_);
                    lean_inc(v_zetaDeltaFVarIds_955_);
                    lean_inc(v_cache_954_);
                    lean_inc(v_mctx_953_);
                    lean_dec(v___x_952_);
                    v___x_959_ = lean_box(0);
                    v_isShared_960_ = v_isSharedCheck_985_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_961_ = lean_ctor_get(v_mctx_953_, 0);
                v_levelAssignDepth_962_ = lean_ctor_get(v_mctx_953_, 1);
                v_lmvarCounter_963_ = lean_ctor_get(v_mctx_953_, 2);
                v_mvarCounter_964_ = lean_ctor_get(v_mctx_953_, 3);
                v_lDecls_965_ = lean_ctor_get(v_mctx_953_, 4);
                v_decls_966_ = lean_ctor_get(v_mctx_953_, 5);
                v_userNames_967_ = lean_ctor_get(v_mctx_953_, 6);
                v_lAssignment_968_ = lean_ctor_get(v_mctx_953_, 7);
                v_eAssignment_969_ = lean_ctor_get(v_mctx_953_, 8);
                v_dAssignment_970_ = lean_ctor_get(v_mctx_953_, 9);
                v_isSharedCheck_984_ = (!lean_is_exclusive(v_mctx_953_)) as u8;
                if v_isSharedCheck_984_ == 0 {
                    v___x_972_ = v_mctx_953_;
                    v_isShared_973_ = v_isSharedCheck_984_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_970_);
                    lean_inc(v_eAssignment_969_);
                    lean_inc(v_lAssignment_968_);
                    lean_inc(v_userNames_967_);
                    lean_inc(v_decls_966_);
                    lean_inc(v_lDecls_965_);
                    lean_inc(v_mvarCounter_964_);
                    lean_inc(v_lmvarCounter_963_);
                    lean_inc(v_levelAssignDepth_962_);
                    lean_inc(v_depth_961_);
                    lean_dec(v_mctx_953_);
                    v___x_972_ = lean_box(0);
                    v_isShared_973_ = v_isSharedCheck_984_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_974_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_eAssignment_969_, v_mvarId_948_, v_val_949_);
                if v_isShared_973_ == 0 {
                    lean_ctor_set(v___x_972_, 8, v___x_974_);
                    v___x_976_ = v___x_972_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_983_, 0, v_depth_961_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 1, v_levelAssignDepth_962_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 2, v_lmvarCounter_963_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 3, v_mvarCounter_964_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 4, v_lDecls_965_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 5, v_decls_966_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 6, v_userNames_967_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 7, v_lAssignment_968_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 8, v___x_974_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 9, v_dAssignment_970_);
                    v___x_976_ = v_reuseFailAlloc_983_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_960_ == 0 {
                    lean_ctor_set(v___x_959_, 0, v___x_976_);
                    v___x_978_ = v___x_959_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_982_, 0, v___x_976_);
                    lean_ctor_set(v_reuseFailAlloc_982_, 1, v_cache_954_);
                    lean_ctor_set(v_reuseFailAlloc_982_, 2, v_zetaDeltaFVarIds_955_);
                    lean_ctor_set(v_reuseFailAlloc_982_, 3, v_postponed_956_);
                    lean_ctor_set(v_reuseFailAlloc_982_, 4, v_diag_957_);
                    v___x_978_ = v_reuseFailAlloc_982_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_979_ = lean_st_ref_set(v___y_950_, v___x_978_);
                v___x_980_ = lean_box(0);
                v___x_981_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_981_, 0, v___x_980_);
                return v___x_981_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg___boxed(
    mut v_mvarId_986_: *mut LeanObject,
    mut v_val_987_: *mut LeanObject,
    mut v___y_988_: *mut LeanObject,
    mut v___y_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_990_: *mut LeanObject = core::ptr::null_mut();
    v_res_990_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_986_, v_val_987_, v___y_988_);
    lean_dec(v___y_988_);
    return v_res_990_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1() -> *mut LeanObject
{
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    v___x_992_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0;
    v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
    return v___x_993_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9() -> *mut LeanObject
{
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1005_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8;
    v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(
    mut v_mvar_1007_: *mut LeanObject,
    mut v_a_1008_: *mut LeanObject,
    mut v_a_1009_: *mut LeanObject,
    mut v_a_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1040_: u8 = 0;
    let mut v_arg_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: u8 = 0;
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_unused_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1085_: u8 = 0;
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut v_a_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1097_: u8 = 0;
    let mut v_reuseFailAlloc_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_unused_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1106_: u8 = 0;
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvar_1007_);
                v___x_1020_ =
                    l_Lean_MVarId_getType(v_mvar_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
                if lean_obj_tag(v___x_1020_) == 0 {
                    v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
                    lean_inc(v_a_1021_);
                    lean_dec_ref_known(v___x_1020_, 1);
                    v___x_1022_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_a_1021_, v_a_1009_);
                    v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
                    lean_inc(v_a_1023_);
                    lean_dec_ref(v___x_1022_);
                    v___x_1024_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1023_);
                    lean_dec(v_a_1023_);
                    if lean_obj_tag(v___x_1024_) == 1 {
                        v_val_1025_ = lean_ctor_get(v___x_1024_, 0);
                        lean_inc(v_val_1025_);
                        lean_dec_ref_known(v___x_1024_, 1);
                        v_target_1026_ = lean_ctor_get(v_val_1025_, 3);
                        lean_inc_ref(v_target_1026_);
                        if lean_obj_tag(v_target_1026_) == 5 {
                            v_fn_1027_ = lean_ctor_get(v_target_1026_, 0);
                            lean_inc_ref(v_fn_1027_);
                            if lean_obj_tag(v_fn_1027_) == 5 {
                                v_fn_1028_ = lean_ctor_get(v_fn_1027_, 0);
                                lean_inc_ref(v_fn_1028_);
                                if lean_obj_tag(v_fn_1028_) == 5 {
                                    v_fn_1029_ = lean_ctor_get(v_fn_1028_, 0);
                                    if lean_obj_tag(v_fn_1029_) == 4 {
                                        v_declName_1030_ = lean_ctor_get(v_fn_1029_, 0);
                                        lean_inc(v_declName_1030_);
                                        if lean_obj_tag(v_declName_1030_) == 1 {
                                            v_pre_1031_ = lean_ctor_get(v_declName_1030_, 0);
                                            lean_inc(v_pre_1031_);
                                            if lean_obj_tag(v_pre_1031_) == 1 {
                                                v_pre_1032_ = lean_ctor_get(v_pre_1031_, 0);
                                                lean_inc(v_pre_1032_);
                                                if lean_obj_tag(v_pre_1032_) == 1 {
                                                    v_pre_1033_ = lean_ctor_get(v_pre_1032_, 0);
                                                    lean_inc(v_pre_1033_);
                                                    if lean_obj_tag(v_pre_1033_) == 1 {
                                                        v_pre_1034_ = lean_ctor_get(v_pre_1033_, 0);
                                                        lean_inc(v_pre_1034_);
                                                        if lean_obj_tag(v_pre_1034_) == 0 {
                                                            v_u_1035_ =
                                                                lean_ctor_get(v_val_1025_, 0);
                                                            v_00_u03c3s_1036_ =
                                                                lean_ctor_get(v_val_1025_, 1);
                                                            v_hyps_1037_ =
                                                                lean_ctor_get(v_val_1025_, 2);
                                                            v_isSharedCheck_1099_ =
                                                                (!lean_is_exclusive(v_val_1025_))
                                                                    as u8;
                                                            if v_isSharedCheck_1099_ == 0 {
                                                                v_unused_1100_ =
                                                                    lean_ctor_get(v_val_1025_, 3);
                                                                lean_dec(v_unused_1100_);
                                                                v___x_1039_ = v_val_1025_;
                                                                v_isShared_1040_ =
                                                                    v_isSharedCheck_1099_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_hyps_1037_);
                                                                lean_inc(v_00_u03c3s_1036_);
                                                                lean_inc(v_u_1035_);
                                                                lean_dec(v_val_1025_);
                                                                v___x_1039_ = lean_box(0);
                                                                v_isShared_1040_ =
                                                                    v_isSharedCheck_1099_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v_pre_1034_);
                                                            lean_dec_ref_known(v_pre_1033_, 2);
                                                            lean_dec_ref_known(v_pre_1032_, 2);
                                                            lean_dec_ref_known(v_pre_1031_, 2);
                                                            lean_dec_ref_known(v_declName_1030_, 2);
                                                            lean_dec_ref_known(v_fn_1028_, 2);
                                                            lean_dec_ref_known(v_fn_1027_, 2);
                                                            lean_dec_ref_known(v_target_1026_, 2);
                                                            lean_dec(v_val_1025_);
                                                            lean_dec(v_mvar_1007_);
                                                            v___y_1014_ = v_a_1008_;
                                                            v___y_1015_ = v_a_1009_;
                                                            v___y_1016_ = v_a_1010_;
                                                            v___y_1017_ = v_a_1011_;
                                                            state = 1;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v_pre_1033_);
                                                        lean_dec_ref_known(v_pre_1032_, 2);
                                                        lean_dec_ref_known(v_pre_1031_, 2);
                                                        lean_dec_ref_known(v_declName_1030_, 2);
                                                        lean_dec_ref_known(v_fn_1028_, 2);
                                                        lean_dec_ref_known(v_fn_1027_, 2);
                                                        lean_dec_ref_known(v_target_1026_, 2);
                                                        lean_dec(v_val_1025_);
                                                        lean_dec(v_mvar_1007_);
                                                        v___y_1014_ = v_a_1008_;
                                                        v___y_1015_ = v_a_1009_;
                                                        v___y_1016_ = v_a_1010_;
                                                        v___y_1017_ = v_a_1011_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v_pre_1031_, 2);
                                                    lean_dec(v_pre_1032_);
                                                    lean_dec_ref_known(v_declName_1030_, 2);
                                                    lean_dec_ref_known(v_fn_1028_, 2);
                                                    lean_dec_ref_known(v_fn_1027_, 2);
                                                    lean_dec_ref_known(v_target_1026_, 2);
                                                    lean_dec(v_val_1025_);
                                                    lean_dec(v_mvar_1007_);
                                                    v___y_1014_ = v_a_1008_;
                                                    v___y_1015_ = v_a_1009_;
                                                    v___y_1016_ = v_a_1010_;
                                                    v___y_1017_ = v_a_1011_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_pre_1031_);
                                                lean_dec_ref_known(v_declName_1030_, 2);
                                                lean_dec_ref_known(v_fn_1028_, 2);
                                                lean_dec_ref_known(v_fn_1027_, 2);
                                                lean_dec_ref_known(v_target_1026_, 2);
                                                lean_dec(v_val_1025_);
                                                lean_dec(v_mvar_1007_);
                                                v___y_1014_ = v_a_1008_;
                                                v___y_1015_ = v_a_1009_;
                                                v___y_1016_ = v_a_1010_;
                                                v___y_1017_ = v_a_1011_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_declName_1030_);
                                            lean_dec_ref_known(v_fn_1028_, 2);
                                            lean_dec_ref_known(v_fn_1027_, 2);
                                            lean_dec_ref_known(v_target_1026_, 2);
                                            lean_dec(v_val_1025_);
                                            lean_dec(v_mvar_1007_);
                                            v___y_1014_ = v_a_1008_;
                                            v___y_1015_ = v_a_1009_;
                                            v___y_1016_ = v_a_1010_;
                                            v___y_1017_ = v_a_1011_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_fn_1028_, 2);
                                        lean_dec_ref_known(v_fn_1027_, 2);
                                        lean_dec_ref_known(v_target_1026_, 2);
                                        lean_dec(v_val_1025_);
                                        lean_dec(v_mvar_1007_);
                                        v___y_1014_ = v_a_1008_;
                                        v___y_1015_ = v_a_1009_;
                                        v___y_1016_ = v_a_1010_;
                                        v___y_1017_ = v_a_1011_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_fn_1028_);
                                    lean_dec_ref_known(v_fn_1027_, 2);
                                    lean_dec_ref_known(v_target_1026_, 2);
                                    lean_dec(v_val_1025_);
                                    lean_dec(v_mvar_1007_);
                                    v___y_1014_ = v_a_1008_;
                                    v___y_1015_ = v_a_1009_;
                                    v___y_1016_ = v_a_1010_;
                                    v___y_1017_ = v_a_1011_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_target_1026_, 2);
                                lean_dec_ref(v_fn_1027_);
                                lean_dec(v_val_1025_);
                                lean_dec(v_mvar_1007_);
                                v___y_1014_ = v_a_1008_;
                                v___y_1015_ = v_a_1009_;
                                v___y_1016_ = v_a_1010_;
                                v___y_1017_ = v_a_1011_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_target_1026_);
                            lean_dec(v_val_1025_);
                            lean_dec(v_mvar_1007_);
                            v___y_1014_ = v_a_1008_;
                            v___y_1015_ = v_a_1009_;
                            v___y_1016_ = v_a_1010_;
                            v___y_1017_ = v_a_1011_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1024_);
                        lean_dec(v_mvar_1007_);
                        v___x_1101_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9_once
                            ),
                            _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9,
                        );
                        v___x_1102_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_1101_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
                        return v___x_1102_;
                    }
                } else {
                    lean_dec(v_mvar_1007_);
                    v_a_1103_ = lean_ctor_get(v___x_1020_, 0);
                    v_isSharedCheck_1110_ = (!lean_is_exclusive(v___x_1020_)) as u8;
                    if v_isSharedCheck_1110_ == 0 {
                        v___x_1105_ = v___x_1020_;
                        v_isShared_1106_ = v_isSharedCheck_1110_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1103_);
                        lean_dec(v___x_1020_);
                        v___x_1105_ = lean_box(0);
                        v_isShared_1106_ = v_isSharedCheck_1110_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1018_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1,
                );
                v___x_1019_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_1018_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
                return v___x_1019_;
            }
            2 => {
                v_arg_1041_ = lean_ctor_get(v_target_1026_, 1);
                lean_inc_ref(v_arg_1041_);
                lean_dec_ref_known(v_target_1026_, 2);
                v_arg_1042_ = lean_ctor_get(v_fn_1027_, 1);
                lean_inc_ref(v_arg_1042_);
                lean_dec_ref_known(v_fn_1027_, 2);
                v_arg_1043_ = lean_ctor_get(v_fn_1028_, 1);
                lean_inc_ref(v_arg_1043_);
                lean_dec_ref_known(v_fn_1028_, 2);
                v_str_1044_ = lean_ctor_get(v_declName_1030_, 1);
                lean_inc_ref(v_str_1044_);
                lean_dec_ref_known(v_declName_1030_, 2);
                v_str_1045_ = lean_ctor_get(v_pre_1031_, 1);
                lean_inc_ref(v_str_1045_);
                lean_dec_ref_known(v_pre_1031_, 2);
                v_str_1046_ = lean_ctor_get(v_pre_1032_, 1);
                lean_inc_ref(v_str_1046_);
                lean_dec_ref_known(v_pre_1032_, 2);
                v_str_1047_ = lean_ctor_get(v_pre_1033_, 1);
                lean_inc_ref(v_str_1047_);
                lean_dec_ref_known(v_pre_1033_, 2);
                v___x_1048_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2;
                v___x_1049_ = lean_string_dec_eq(v_str_1047_, v___x_1048_);
                lean_dec_ref(v_str_1047_);
                if v___x_1049_ == 0 {
                    lean_dec_ref(v_str_1046_);
                    lean_dec_ref(v_str_1045_);
                    lean_dec_ref(v_str_1044_);
                    lean_dec_ref(v_arg_1043_);
                    lean_dec_ref(v_arg_1042_);
                    lean_dec_ref(v_arg_1041_);
                    lean_del_object(v___x_1039_);
                    lean_dec_ref(v_hyps_1037_);
                    lean_dec_ref(v_00_u03c3s_1036_);
                    lean_dec(v_u_1035_);
                    lean_dec(v_mvar_1007_);
                    v___y_1014_ = v_a_1008_;
                    v___y_1015_ = v_a_1009_;
                    v___y_1016_ = v_a_1010_;
                    v___y_1017_ = v_a_1011_;
                    state = 1;
                    continue;
                } else {
                    v___x_1050_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3;
                    v___x_1051_ = lean_string_dec_eq(v_str_1046_, v___x_1050_);
                    lean_dec_ref(v_str_1046_);
                    if v___x_1051_ == 0 {
                        lean_dec_ref(v_str_1045_);
                        lean_dec_ref(v_str_1044_);
                        lean_dec_ref(v_arg_1043_);
                        lean_dec_ref(v_arg_1042_);
                        lean_dec_ref(v_arg_1041_);
                        lean_del_object(v___x_1039_);
                        lean_dec_ref(v_hyps_1037_);
                        lean_dec_ref(v_00_u03c3s_1036_);
                        lean_dec(v_u_1035_);
                        lean_dec(v_mvar_1007_);
                        v___y_1014_ = v_a_1008_;
                        v___y_1015_ = v_a_1009_;
                        v___y_1016_ = v_a_1010_;
                        v___y_1017_ = v_a_1011_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1052_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4;
                        v___x_1053_ = lean_string_dec_eq(v_str_1045_, v___x_1052_);
                        lean_dec_ref(v_str_1045_);
                        if v___x_1053_ == 0 {
                            lean_dec_ref(v_str_1044_);
                            lean_dec_ref(v_arg_1043_);
                            lean_dec_ref(v_arg_1042_);
                            lean_dec_ref(v_arg_1041_);
                            lean_del_object(v___x_1039_);
                            lean_dec_ref(v_hyps_1037_);
                            lean_dec_ref(v_00_u03c3s_1036_);
                            lean_dec(v_u_1035_);
                            lean_dec(v_mvar_1007_);
                            v___y_1014_ = v_a_1008_;
                            v___y_1015_ = v_a_1009_;
                            v___y_1016_ = v_a_1010_;
                            v___y_1017_ = v_a_1011_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1054_ =
                                l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5;
                            v___x_1055_ = lean_string_dec_eq(v_str_1044_, v___x_1054_);
                            lean_dec_ref(v_str_1044_);
                            if v___x_1055_ == 0 {
                                lean_dec_ref(v_arg_1043_);
                                lean_dec_ref(v_arg_1042_);
                                lean_dec_ref(v_arg_1041_);
                                lean_del_object(v___x_1039_);
                                lean_dec_ref(v_hyps_1037_);
                                lean_dec_ref(v_00_u03c3s_1036_);
                                lean_dec(v_u_1035_);
                                lean_dec(v_mvar_1007_);
                                v___y_1014_ = v_a_1008_;
                                v___y_1015_ = v_a_1009_;
                                v___y_1016_ = v_a_1010_;
                                v___y_1017_ = v_a_1011_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc_ref(v_arg_1042_);
                                lean_inc_ref(v_hyps_1037_);
                                lean_inc_ref(v_00_u03c3s_1036_);
                                lean_inc(v_u_1035_);
                                if v_isShared_1040_ == 0 {
                                    lean_ctor_set(v___x_1039_, 3, v_arg_1042_);
                                    v___x_1057_ = v___x_1039_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 4, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_u_1035_);
                                    lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_00_u03c3s_1036_);
                                    lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_hyps_1037_);
                                    lean_ctor_set(v_reuseFailAlloc_1098_, 3, v_arg_1042_);
                                    v___x_1057_ = v_reuseFailAlloc_1098_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_1058_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1057_);
                v___x_1059_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_1058_,
                    v_pre_1034_,
                    v_a_1008_,
                    v_a_1009_,
                    v_a_1010_,
                    v_a_1011_,
                );
                if lean_obj_tag(v___x_1059_) == 0 {
                    v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
                    lean_inc(v_a_1060_);
                    lean_dec_ref_known(v___x_1059_, 1);
                    lean_inc_ref(v_arg_1041_);
                    lean_inc_ref(v_hyps_1037_);
                    lean_inc(v_u_1035_);
                    v___x_1061_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v___x_1061_, 0, v_u_1035_);
                    lean_ctor_set(v___x_1061_, 1, v_00_u03c3s_1036_);
                    lean_ctor_set(v___x_1061_, 2, v_hyps_1037_);
                    lean_ctor_set(v___x_1061_, 3, v_arg_1041_);
                    v___x_1062_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_1061_);
                    v___x_1063_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_1062_,
                        v_pre_1034_,
                        v_a_1008_,
                        v_a_1009_,
                        v_a_1010_,
                        v_a_1011_,
                    );
                    if lean_obj_tag(v___x_1063_) == 0 {
                        v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
                        lean_inc_n(v_a_1064_, 2);
                        lean_dec_ref_known(v___x_1063_, 1);
                        v___x_1065_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7;
                        v___x_1066_ = lean_box(0);
                        v___x_1067_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1067_, 0, v_u_1035_);
                        lean_ctor_set(v___x_1067_, 1, v___x_1066_);
                        v___x_1068_ = l_Lean_mkConst(v___x_1065_, v___x_1067_);
                        lean_inc(v_a_1060_);
                        v___x_1069_ = l_Lean_mkApp6(
                            v___x_1068_,
                            v_arg_1043_,
                            v_hyps_1037_,
                            v_arg_1042_,
                            v_arg_1041_,
                            v_a_1060_,
                            v_a_1064_,
                        );
                        v___x_1070_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvar_1007_, v___x_1069_, v_a_1009_);
                        v_isSharedCheck_1080_ = (!lean_is_exclusive(v___x_1070_)) as u8;
                        if v_isSharedCheck_1080_ == 0 {
                            v_unused_1081_ = lean_ctor_get(v___x_1070_, 0);
                            lean_dec(v_unused_1081_);
                            v___x_1072_ = v___x_1070_;
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___x_1070_);
                            v___x_1072_ = lean_box(0);
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1060_);
                        lean_dec_ref(v_arg_1043_);
                        lean_dec_ref(v_arg_1042_);
                        lean_dec_ref(v_arg_1041_);
                        lean_dec_ref(v_hyps_1037_);
                        lean_dec(v_u_1035_);
                        lean_dec(v_mvar_1007_);
                        v_a_1082_ = lean_ctor_get(v___x_1063_, 0);
                        v_isSharedCheck_1089_ = (!lean_is_exclusive(v___x_1063_)) as u8;
                        if v_isSharedCheck_1089_ == 0 {
                            v___x_1084_ = v___x_1063_;
                            v_isShared_1085_ = v_isSharedCheck_1089_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1082_);
                            lean_dec(v___x_1063_);
                            v___x_1084_ = lean_box(0);
                            v_isShared_1085_ = v_isSharedCheck_1089_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_arg_1043_);
                    lean_dec_ref(v_arg_1042_);
                    lean_dec_ref(v_arg_1041_);
                    lean_dec_ref(v_hyps_1037_);
                    lean_dec_ref(v_00_u03c3s_1036_);
                    lean_dec(v_u_1035_);
                    lean_dec(v_mvar_1007_);
                    v_a_1090_ = lean_ctor_get(v___x_1059_, 0);
                    v_isSharedCheck_1097_ = (!lean_is_exclusive(v___x_1059_)) as u8;
                    if v_isSharedCheck_1097_ == 0 {
                        v___x_1092_ = v___x_1059_;
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1090_);
                        lean_dec(v___x_1059_);
                        v___x_1092_ = lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1097_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1074_ = l_Lean_Expr_mvarId_x21(v_a_1060_);
                lean_dec(v_a_1060_);
                v___x_1075_ = l_Lean_Expr_mvarId_x21(v_a_1064_);
                lean_dec(v_a_1064_);
                v___x_1076_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1076_, 0, v___x_1074_);
                lean_ctor_set(v___x_1076_, 1, v___x_1075_);
                if v_isShared_1073_ == 0 {
                    lean_ctor_set(v___x_1072_, 0, v___x_1076_);
                    v___x_1078_ = v___x_1072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1078_;
            }
            6 => {
                if v_isShared_1085_ == 0 {
                    v___x_1087_ = v___x_1084_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1082_);
                    v___x_1087_ = v_reuseFailAlloc_1088_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1087_;
            }
            8 => {
                if v_isShared_1093_ == 0 {
                    v___x_1095_ = v___x_1092_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
                    v___x_1095_ = v_reuseFailAlloc_1096_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1095_;
            }
            10 => {
                if v_isShared_1106_ == 0 {
                    v___x_1108_ = v___x_1105_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
                    v___x_1108_ = v_reuseFailAlloc_1109_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___boxed(
    mut v_mvar_1111_: *mut LeanObject,
    mut v_a_1112_: *mut LeanObject,
    mut v_a_1113_: *mut LeanObject,
    mut v_a_1114_: *mut LeanObject,
    mut v_a_1115_: *mut LeanObject,
    mut v_a_1116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1117_: *mut LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(
        v_mvar_1111_,
        v_a_1112_,
        v_a_1113_,
        v_a_1114_,
        v_a_1115_,
    );
    lean_dec(v_a_1115_);
    lean_dec_ref(v_a_1114_);
    lean_dec(v_a_1113_);
    lean_dec_ref(v_a_1112_);
    return v_res_1117_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(
    mut v_00_u03b1_1118_: *mut LeanObject,
    mut v_msg_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    v___x_1125_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(
            v_msg_1119_,
            v___y_1120_,
            v___y_1121_,
            v___y_1122_,
            v___y_1123_,
        );
    return v___x_1125_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___boxed(
    mut v_00_u03b1_1126_: *mut LeanObject,
    mut v_msg_1127_: *mut LeanObject,
    mut v___y_1128_: *mut LeanObject,
    mut v___y_1129_: *mut LeanObject,
    mut v___y_1130_: *mut LeanObject,
    mut v___y_1131_: *mut LeanObject,
    mut v___y_1132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1133_: *mut LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(
        v_00_u03b1_1126_,
        v_msg_1127_,
        v___y_1128_,
        v___y_1129_,
        v___y_1130_,
        v___y_1131_,
    );
    lean_dec(v___y_1131_);
    lean_dec_ref(v___y_1130_);
    lean_dec(v___y_1129_);
    lean_dec_ref(v___y_1128_);
    return v_res_1133_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(
    mut v_mvarId_1134_: *mut LeanObject,
    mut v_val_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
    mut v___y_1138_: *mut LeanObject,
    mut v___y_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    v___x_1141_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_1134_, v_val_1135_, v___y_1137_);
    return v___x_1141_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___boxed(
    mut v_mvarId_1142_: *mut LeanObject,
    mut v_val_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
    mut v___y_1148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1149_: *mut LeanObject = core::ptr::null_mut();
    v_res_1149_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(
            v_mvarId_1142_,
            v_val_1143_,
            v___y_1144_,
            v___y_1145_,
            v___y_1146_,
            v___y_1147_,
        );
    lean_dec(v___y_1147_);
    lean_dec_ref(v___y_1146_);
    lean_dec(v___y_1145_);
    lean_dec_ref(v___y_1144_);
    return v_res_1149_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3(
    mut v_00_u03b2_1150_: *mut LeanObject,
    mut v_x_1151_: *mut LeanObject,
    mut v_x_1152_: *mut LeanObject,
    mut v_x_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    v___x_1154_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_x_1151_, v_x_1152_, v_x_1153_);
    return v___x_1154_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1155_: *mut LeanObject,
    mut v_x_1156_: *mut LeanObject,
    mut v_x_1157_: usize,
    mut v_x_1158_: usize,
    mut v_x_1159_: *mut LeanObject,
    mut v_x_1160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_1156_, v_x_1157_, v_x_1158_, v_x_1159_, v_x_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_1162_: *mut LeanObject,
    mut v_x_1163_: *mut LeanObject,
    mut v_x_1164_: *mut LeanObject,
    mut v_x_1165_: *mut LeanObject,
    mut v_x_1166_: *mut LeanObject,
    mut v_x_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4087__boxed_1168_: usize = 0;
    let mut v_x_4088__boxed_1169_: usize = 0;
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_x_4087__boxed_1168_ = lean_unbox_usize(v_x_1164_);
    lean_dec(v_x_1164_);
    v_x_4088__boxed_1169_ = lean_unbox_usize(v_x_1165_);
    lean_dec(v_x_1165_);
    v_res_1170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(v_00_u03b2_1162_, v_x_1163_, v_x_4087__boxed_1168_, v_x_4088__boxed_1169_, v_x_1166_, v_x_1167_);
    return v_res_1170_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1171_: *mut LeanObject,
    mut v_n_1172_: *mut LeanObject,
    mut v_k_1173_: *mut LeanObject,
    mut v_v_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_1172_, v_k_1173_, v_v_1174_);
    return v___x_1175_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1176_: *mut LeanObject,
    mut v_depth_1177_: usize,
    mut v_keys_1178_: *mut LeanObject,
    mut v_vals_1179_: *mut LeanObject,
    mut v_heq_1180_: *mut LeanObject,
    mut v_i_1181_: *mut LeanObject,
    mut v_entries_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    v___x_1183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_1177_, v_keys_1178_, v_vals_1179_, v_i_1181_, v_entries_1182_);
    return v___x_1183_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_1184_: *mut LeanObject,
    mut v_depth_1185_: *mut LeanObject,
    mut v_keys_1186_: *mut LeanObject,
    mut v_vals_1187_: *mut LeanObject,
    mut v_heq_1188_: *mut LeanObject,
    mut v_i_1189_: *mut LeanObject,
    mut v_entries_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1191_: usize = 0;
    let mut v_res_1192_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1191_ = lean_unbox_usize(v_depth_1185_);
    lean_dec(v_depth_1185_);
    v_res_1192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_1184_, v_depth_boxed_1191_, v_keys_1186_, v_vals_1187_, v_heq_1188_, v_i_1189_, v_entries_1190_);
    lean_dec_ref(v_vals_1187_);
    lean_dec_ref(v_keys_1186_);
    return v_res_1192_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6(
    mut v_00_u03b2_1193_: *mut LeanObject,
    mut v_x_1194_: *mut LeanObject,
    mut v_x_1195_: *mut LeanObject,
    mut v_x_1196_: *mut LeanObject,
    mut v_x_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_1194_, v_x_1195_, v_x_1196_, v_x_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(
    mut v_x_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
    mut v___y_1201_: *mut LeanObject,
    mut v___y_1202_: *mut LeanObject,
    mut v___y_1203_: *mut LeanObject,
    mut v___y_1204_: *mut LeanObject,
    mut v___y_1205_: *mut LeanObject,
    mut v___y_1206_: *mut LeanObject,
    mut v___y_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1203_);
    lean_inc_ref(v___y_1202_);
    lean_inc(v___y_1201_);
    lean_inc_ref(v___y_1200_);
    v___x_1209_ = lean_apply_9(
        v_x_1199_,
        v___y_1200_,
        v___y_1201_,
        v___y_1202_,
        v___y_1203_,
        v___y_1204_,
        v___y_1205_,
        v___y_1206_,
        v___y_1207_,
        lean_box(0),
    );
    return v___x_1209_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed(
    mut v_x_1210_: *mut LeanObject,
    mut v___y_1211_: *mut LeanObject,
    mut v___y_1212_: *mut LeanObject,
    mut v___y_1213_: *mut LeanObject,
    mut v___y_1214_: *mut LeanObject,
    mut v___y_1215_: *mut LeanObject,
    mut v___y_1216_: *mut LeanObject,
    mut v___y_1217_: *mut LeanObject,
    mut v___y_1218_: *mut LeanObject,
    mut v___y_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1220_: *mut LeanObject = core::ptr::null_mut();
    v_res_1220_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
    lean_dec(v___y_1214_);
    lean_dec_ref(v___y_1213_);
    lean_dec(v___y_1212_);
    lean_dec_ref(v___y_1211_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(
    mut v_mvarId_1221_: *mut LeanObject,
    mut v_x_1222_: *mut LeanObject,
    mut v___y_1223_: *mut LeanObject,
    mut v___y_1224_: *mut LeanObject,
    mut v___y_1225_: *mut LeanObject,
    mut v___y_1226_: *mut LeanObject,
    mut v___y_1227_: *mut LeanObject,
    mut v___y_1228_: *mut LeanObject,
    mut v___y_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1241_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1226_);
                lean_inc_ref(v___y_1225_);
                lean_inc(v___y_1224_);
                lean_inc_ref(v___y_1223_);
                v___f_1232_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_1232_, 0, v_x_1222_);
                lean_closure_set(v___f_1232_, 1, v___y_1223_);
                lean_closure_set(v___f_1232_, 2, v___y_1224_);
                lean_closure_set(v___f_1232_, 3, v___y_1225_);
                lean_closure_set(v___f_1232_, 4, v___y_1226_);
                v___x_1233_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_1221_,
                    v___f_1232_,
                    v___y_1227_,
                    v___y_1228_,
                    v___y_1229_,
                    v___y_1230_,
                );
                if lean_obj_tag(v___x_1233_) == 0 {
                    return v___x_1233_;
                } else {
                    v_a_1234_ = lean_ctor_get(v___x_1233_, 0);
                    v_isSharedCheck_1241_ = (!lean_is_exclusive(v___x_1233_)) as u8;
                    if v_isSharedCheck_1241_ == 0 {
                        v___x_1236_ = v___x_1233_;
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1234_);
                        lean_dec(v___x_1233_);
                        v___x_1236_ = lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1241_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1237_ == 0 {
                    v___x_1239_ = v___x_1236_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
                    v___x_1239_ = v_reuseFailAlloc_1240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___boxed(
    mut v_mvarId_1242_: *mut LeanObject,
    mut v_x_1243_: *mut LeanObject,
    mut v___y_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
    mut v___y_1250_: *mut LeanObject,
    mut v___y_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1253_: *mut LeanObject = core::ptr::null_mut();
    v_res_1253_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_1242_, v_x_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
    lean_dec(v___y_1251_);
    lean_dec_ref(v___y_1250_);
    lean_dec(v___y_1249_);
    lean_dec_ref(v___y_1248_);
    lean_dec(v___y_1247_);
    lean_dec_ref(v___y_1246_);
    lean_dec(v___y_1245_);
    lean_dec_ref(v___y_1244_);
    return v_res_1253_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(
    mut v_00_u03b1_1254_: *mut LeanObject,
    mut v_mvarId_1255_: *mut LeanObject,
    mut v_x_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
    mut v___y_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    v___x_1266_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_1255_, v_x_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
    return v___x_1266_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___boxed(
    mut v_00_u03b1_1267_: *mut LeanObject,
    mut v_mvarId_1268_: *mut LeanObject,
    mut v_x_1269_: *mut LeanObject,
    mut v___y_1270_: *mut LeanObject,
    mut v___y_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1279_: *mut LeanObject = core::ptr::null_mut();
    v_res_1279_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(
            v_00_u03b1_1267_,
            v_mvarId_1268_,
            v_x_1269_,
            v___y_1270_,
            v___y_1271_,
            v___y_1272_,
            v___y_1273_,
            v___y_1274_,
            v___y_1275_,
            v___y_1276_,
            v___y_1277_,
        );
    lean_dec(v___y_1277_);
    lean_dec_ref(v___y_1276_);
    lean_dec(v___y_1275_);
    lean_dec_ref(v___y_1274_);
    lean_dec(v___y_1273_);
    lean_dec_ref(v___y_1272_);
    lean_dec(v___y_1271_);
    lean_dec_ref(v___y_1270_);
    return v_res_1279_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(
    mut v_a_1280_: *mut LeanObject,
    mut v___y_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
    mut v___y_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1303_: u8 = 0;
    let mut v_a_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1307_: u8 = 0;
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1290_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(
                    v_a_1280_,
                    v___y_1285_,
                    v___y_1286_,
                    v___y_1287_,
                    v___y_1288_,
                );
                if lean_obj_tag(v___x_1290_) == 0 {
                    v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
                    lean_inc(v_a_1291_);
                    lean_dec_ref_known(v___x_1290_, 1);
                    v_fst_1292_ = lean_ctor_get(v_a_1291_, 0);
                    v_snd_1293_ = lean_ctor_get(v_a_1291_, 1);
                    v_isSharedCheck_1303_ = (!lean_is_exclusive(v_a_1291_)) as u8;
                    if v_isSharedCheck_1303_ == 0 {
                        v___x_1295_ = v_a_1291_;
                        v_isShared_1296_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1293_);
                        lean_inc(v_fst_1292_);
                        lean_dec(v_a_1291_);
                        v___x_1295_ = lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1303_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1304_ = lean_ctor_get(v___x_1290_, 0);
                    v_isSharedCheck_1311_ = (!lean_is_exclusive(v___x_1290_)) as u8;
                    if v_isSharedCheck_1311_ == 0 {
                        v___x_1306_ = v___x_1290_;
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1304_);
                        lean_dec(v___x_1290_);
                        v___x_1306_ = lean_box(0);
                        v_isShared_1307_ = v_isSharedCheck_1311_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1297_ = lean_box(0);
                if v_isShared_1296_ == 0 {
                    lean_ctor_set_tag(v___x_1295_, 1);
                    lean_ctor_set(v___x_1295_, 1, v___x_1297_);
                    lean_ctor_set(v___x_1295_, 0, v_snd_1293_);
                    v___x_1299_ = v___x_1295_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_snd_1293_);
                    lean_ctor_set(v_reuseFailAlloc_1302_, 1, v___x_1297_);
                    v___x_1299_ = v_reuseFailAlloc_1302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1300_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1300_, 0, v_fst_1292_);
                lean_ctor_set(v___x_1300_, 1, v___x_1299_);
                v___x_1301_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_1300_,
                    v___y_1282_,
                    v___y_1285_,
                    v___y_1286_,
                    v___y_1287_,
                    v___y_1288_,
                );
                return v___x_1301_;
            }
            3 => {
                if v_isShared_1307_ == 0 {
                    v___x_1309_ = v___x_1306_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
                    v___x_1309_ = v_reuseFailAlloc_1310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed(
    mut v_a_1312_: *mut LeanObject,
    mut v___y_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
    mut v___y_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
    mut v___y_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1322_: *mut LeanObject = core::ptr::null_mut();
    v_res_1322_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(
        v_a_1312_,
        v___y_1313_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
        v___y_1318_,
        v___y_1319_,
        v___y_1320_,
    );
    lean_dec(v___y_1320_);
    lean_dec_ref(v___y_1319_);
    lean_dec(v___y_1318_);
    lean_dec_ref(v___y_1317_);
    lean_dec(v___y_1316_);
    lean_dec_ref(v___y_1315_);
    lean_dec(v___y_1314_);
    lean_dec_ref(v___y_1313_);
    return v_res_1322_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(
    mut v_a_1323_: *mut LeanObject,
    mut v_a_1324_: *mut LeanObject,
    mut v_a_1325_: *mut LeanObject,
    mut v_a_1326_: *mut LeanObject,
    mut v_a_1327_: *mut LeanObject,
    mut v_a_1328_: *mut LeanObject,
    mut v_a_1329_: *mut LeanObject,
    mut v_a_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1332_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_1324_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_,
                );
                if lean_obj_tag(v___x_1332_) == 0 {
                    v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
                    lean_inc_n(v_a_1333_, 2);
                    lean_dec_ref_known(v___x_1332_, 1);
                    v___f_1334_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_1334_, 0, v_a_1333_);
                    v___x_1335_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_a_1333_, v___f_1334_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
                    return v___x_1335_;
                } else {
                    v_a_1336_ = lean_ctor_get(v___x_1332_, 0);
                    v_isSharedCheck_1343_ = (!lean_is_exclusive(v___x_1332_)) as u8;
                    if v_isSharedCheck_1343_ == 0 {
                        v___x_1338_ = v___x_1332_;
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1336_);
                        lean_dec(v___x_1332_);
                        v___x_1338_ = lean_box(0);
                        v_isShared_1339_ = v_isSharedCheck_1343_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1339_ == 0 {
                    v___x_1341_ = v___x_1338_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___boxed(
    mut v_a_1344_: *mut LeanObject,
    mut v_a_1345_: *mut LeanObject,
    mut v_a_1346_: *mut LeanObject,
    mut v_a_1347_: *mut LeanObject,
    mut v_a_1348_: *mut LeanObject,
    mut v_a_1349_: *mut LeanObject,
    mut v_a_1350_: *mut LeanObject,
    mut v_a_1351_: *mut LeanObject,
    mut v_a_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1353_: *mut LeanObject = core::ptr::null_mut();
    v_res_1353_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(
        v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_,
    );
    lean_dec(v_a_1351_);
    lean_dec_ref(v_a_1350_);
    lean_dec(v_a_1349_);
    lean_dec_ref(v_a_1348_);
    lean_dec(v_a_1347_);
    lean_dec_ref(v_a_1346_);
    lean_dec(v_a_1345_);
    lean_dec_ref(v_a_1344_);
    return v_res_1353_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(
    mut v_x_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
    mut v_a_1357_: *mut LeanObject,
    mut v_a_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
    mut v_a_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1364_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(
        v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_,
    );
    return v___x_1364_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed(
    mut v_x_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
    mut v_a_1367_: *mut LeanObject,
    mut v_a_1368_: *mut LeanObject,
    mut v_a_1369_: *mut LeanObject,
    mut v_a_1370_: *mut LeanObject,
    mut v_a_1371_: *mut LeanObject,
    mut v_a_1372_: *mut LeanObject,
    mut v_a_1373_: *mut LeanObject,
    mut v_a_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(
        v_x_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_,
        v_a_1373_,
    );
    lean_dec(v_a_1373_);
    lean_dec_ref(v_a_1372_);
    lean_dec(v_a_1371_);
    lean_dec_ref(v_a_1370_);
    lean_dec(v_a_1369_);
    lean_dec_ref(v_a_1368_);
    lean_dec(v_a_1367_);
    lean_dec_ref(v_a_1366_);
    lean_dec(v_x_1365_);
    return v_res_1375_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1()
-> *mut LeanObject {
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    v___x_1396_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1397_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4;
    v___x_1398_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8;
    v___x_1399_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_1400_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1396_,
        v___x_1397_,
        v___x_1398_,
        v___x_1399_,
    );
    return v___x_1400_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___boxed(
    mut v_a_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1402_: *mut LeanObject = core::ptr::null_mut();
    v_res_1402_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
    return v_res_1402_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(
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
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
}
