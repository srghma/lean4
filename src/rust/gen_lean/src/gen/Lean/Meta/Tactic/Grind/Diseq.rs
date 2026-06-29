// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Diseq
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Lemmas
use crate::r#gen::Init::Grind::Lemmas::{
    initialize_Init_Grind_Lemmas, runtime_initialize_Init_Grind_Lemmas,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_constLevels_x21, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkOfEqFalseCore;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash,
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent,
    l_Lean_Meta_Grind_instInhabitedGoalM, l_Lean_Meta_Grind_isEqFalse___redArg,
    l_Lean_Meta_Grind_isEqv___redArg, l_Lean_Meta_Grind_mkEqFalseProof,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{lean_usize_sub, lean_usize_to_nat};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_nat_add, lean_nat_dec_lt,
    lean_panic_fn_borrowed,
};
use crate::ffi::lean_st_ref_get;
use crate::ffi::lean_grind_mk_eq_proof;
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value:
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
    m_data: [69, 113, 0],
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value:
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
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value
        ) as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0_value: crate::leanh::LeanStringObject<
    29,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105,
        110, 100, 46, 68, 105, 115, 101, 113, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1_value: crate::leanh::LeanStringObject<
    34,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 68, 105,
        115, 101, 113, 80, 114, 111, 111, 102, 85, 115, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2_value: crate::leanh::LeanStringObject<
    34,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value: crate::leanh::LeanStringObject<
    21,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        110, 101, 95, 111, 102, 95, 110, 101, 95, 111, 102, 95, 101, 113, 95, 114, 105, 103, 104,
        116, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value)
                as *mut crate::leanh::LeanObject,
            15085210600211958602 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value: crate::leanh::LeanStringObject<
    20,
> = crate::leanh::LeanStringObject {
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
        110, 101, 95, 111, 102, 95, 110, 101, 95, 111, 102, 95, 101, 113, 95, 108, 101, 102, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_1: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value)
                as *mut crate::leanh::LeanObject,
            12081245626925201571 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [78, 101, 0],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 121, 109, 109, 0],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value_aux_0: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value)
            as *mut crate::leanh::LeanObject,
        6695605208187598753 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value)
                as *mut crate::leanh::LeanObject,
            6773482220982667626 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProof___closed__0_value: crate::leanh::LeanStringObject<62> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 62,
        m_capacity: 62,
        m_length: 61,
        m_data: [
            105, 110, 116, 101, 114, 110, 97, 108, 32, 96, 103, 114, 105, 110, 100, 96, 32, 101,
            114, 114, 111, 114, 44, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 98, 117,
            105, 108, 100, 32, 100, 105, 115, 101, 113, 117, 97, 108, 105, 116, 121, 32, 112, 114,
            111, 111, 102, 32, 102, 111, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProof___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkDiseqProof___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [10, 97, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProof___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_672_ = l_Lean_Level_ofNat(v___x_671_);
    return v___x_672_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = crate::leanh::lean_box(0);
    v___x_674_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2,
    );
    v___x_675_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_675_, 0, v___x_674_);
    crate::leanh::lean_ctor_set(v___x_675_, 1, v___x_673_);
    return v___x_675_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3,
    );
    v___x_677_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1;
    v___x_678_ = l_Lean_mkConst(v___x_677_, v___x_676_);
    return v___x_678_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = crate::leanh::lean_box(0);
    v___x_683_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6;
    v___x_684_ = l_Lean_Expr_const___override(v___x_683_, v___x_682_);
    return v___x_684_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7,
    );
    v___x_686_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4,
    );
    v___x_687_ = l_Lean_Expr_app___override(v___x_686_, v___x_685_);
    return v___x_687_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq()
-> *mut crate::leanh::LeanObject {
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8,
    );
    return v___x_688_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(
    mut v___x_689_: *mut crate::leanh::LeanObject,
    mut v_keys_690_: *mut crate::leanh::LeanObject,
    mut v_vals_691_: *mut crate::leanh::LeanObject,
    mut v_i_692_: *mut crate::leanh::LeanObject,
    mut v_k_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_694_ = lean_array_get_size(v_keys_690_);
                v___x_695_ = lean_nat_dec_lt(v_i_692_, v___x_694_);
                if v___x_695_ == 0 {
                    crate::leanh::lean_dec_ref(v_k_693_);
                    crate::leanh::lean_dec(v_i_692_);
                    v___x_696_ = crate::leanh::lean_box(0);
                    return v___x_696_;
                } else {
                    v_k_x27_697_ = lean_array_fget_borrowed(v_keys_690_, v_i_692_);
                    crate::leanh::lean_inc(v_k_x27_697_);
                    crate::leanh::lean_inc_ref(v_k_693_);
                    v___x_698_ =
                        l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(
                            v___x_689_,
                            v_k_693_,
                            v_k_x27_697_,
                        );
                    if v___x_698_ == 0 {
                        v___x_699_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_700_ = lean_nat_add(v_i_692_, v___x_699_);
                        crate::leanh::lean_dec(v_i_692_);
                        v_i_692_ = v___x_700_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_693_);
                        v___x_702_ = lean_array_fget_borrowed(v_vals_691_, v_i_692_);
                        crate::leanh::lean_dec(v_i_692_);
                        crate::leanh::lean_inc(v___x_702_);
                        crate::leanh::lean_inc(v_k_x27_697_);
                        v___x_703_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_703_, 0, v_k_x27_697_);
                        crate::leanh::lean_ctor_set(v___x_703_, 1, v___x_702_);
                        v___x_704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_704_, 0, v___x_703_);
                        return v___x_704_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v___x_705_: *mut crate::leanh::LeanObject,
    mut v_keys_706_: *mut crate::leanh::LeanObject,
    mut v_vals_707_: *mut crate::leanh::LeanObject,
    mut v_i_708_: *mut crate::leanh::LeanObject,
    mut v_k_709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_710_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_705_, v_keys_706_, v_vals_707_, v_i_708_, v_k_709_);
    crate::leanh::lean_dec_ref(v_vals_707_);
    crate::leanh::lean_dec_ref(v_keys_706_);
    crate::leanh::lean_dec_ref(v___x_705_);
    return v_res_710_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_711_: usize = 0;
    let mut v___x_712_: usize = 0;
    let mut v___x_713_: usize = 0;
    v___x_711_ = 5usize;
    v___x_712_ = 1usize;
    v___x_713_ = lean_usize_shift_left(v___x_712_, v___x_711_);
    return v___x_713_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: usize = 0;
    v___x_714_ = 1usize;
    v___x_715_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_716_ = lean_usize_sub(v___x_715_, v___x_714_);
    return v___x_716_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(
    mut v___x_717_: *mut crate::leanh::LeanObject,
    mut v_x_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: usize,
    mut v_x_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: usize = 0;
    let mut v___x_724_: usize = 0;
    let mut v___x_725_: usize = 0;
    let mut v_j_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u8 = 0;
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: usize = 0;
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_718_) == 0 {
                    v_es_721_ = crate::leanh::lean_ctor_get(v_x_718_, 0);
                    crate::leanh::lean_inc_ref(v_es_721_);
                    crate::leanh::lean_dec_ref_known(v_x_718_, 1);
                    v___x_722_ = crate::leanh::lean_box(2);
                    v___x_723_ = 5usize;
                    v___x_724_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_725_ = lean_usize_land(v_x_719_, v___x_724_);
                    v_j_726_ = lean_usize_to_nat(v___x_725_);
                    v___x_727_ = lean_array_get(v___x_722_, v_es_721_, v_j_726_);
                    crate::leanh::lean_dec(v_j_726_);
                    crate::leanh::lean_dec_ref(v_es_721_);
                    match crate::leanh::lean_obj_tag(v___x_727_) {
                        0 => {
                            v_key_728_ = crate::leanh::lean_ctor_get(v___x_727_, 0);
                            crate::leanh::lean_inc_n(v_key_728_, 2);
                            v_val_729_ = crate::leanh::lean_ctor_get(v___x_727_, 1);
                            crate::leanh::lean_inc(v_val_729_);
                            crate::leanh::lean_dec_ref_known(v___x_727_, 2);
                            v___x_730_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_717_, v_x_720_, v_key_728_);
                            if v___x_730_ == 0 {
                                crate::leanh::lean_dec(v_val_729_);
                                crate::leanh::lean_dec(v_key_728_);
                                v___x_731_ = crate::leanh::lean_box(0);
                                return v___x_731_;
                            } else {
                                v___x_732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_732_, 0, v_key_728_);
                                crate::leanh::lean_ctor_set(v___x_732_, 1, v_val_729_);
                                v___x_733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_733_, 0, v___x_732_);
                                return v___x_733_;
                            }
                        }
                        1 => {
                            v_node_734_ = crate::leanh::lean_ctor_get(v___x_727_, 0);
                            crate::leanh::lean_inc(v_node_734_);
                            crate::leanh::lean_dec_ref_known(v___x_727_, 1);
                            v___x_735_ = lean_usize_shift_right(v_x_719_, v___x_723_);
                            v_x_718_ = v_node_734_;
                            v_x_719_ = v___x_735_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec_ref(v_x_720_);
                            v___x_737_ = crate::leanh::lean_box(0);
                            return v___x_737_;
                        }
                    }
                } else {
                    v_ks_738_ = crate::leanh::lean_ctor_get(v_x_718_, 0);
                    crate::leanh::lean_inc_ref(v_ks_738_);
                    v_vs_739_ = crate::leanh::lean_ctor_get(v_x_718_, 1);
                    crate::leanh::lean_inc_ref(v_vs_739_);
                    crate::leanh::lean_dec_ref_known(v_x_718_, 2);
                    v___x_740_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_741_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_717_, v_ks_738_, v_vs_739_, v___x_740_, v_x_720_);
                    crate::leanh::lean_dec_ref(v_vs_739_);
                    crate::leanh::lean_dec_ref(v_ks_738_);
                    return v___x_741_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___boxed(
    mut v___x_742_: *mut crate::leanh::LeanObject,
    mut v_x_743_: *mut crate::leanh::LeanObject,
    mut v_x_744_: *mut crate::leanh::LeanObject,
    mut v_x_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4773__boxed_746_: usize = 0;
    let mut v_res_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4773__boxed_746_ = crate::leanh::lean_unbox_usize(v_x_744_);
    crate::leanh::lean_dec(v_x_744_);
    v_res_747_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_742_, v_x_743_, v_x_4773__boxed_746_, v_x_745_);
    crate::leanh::lean_dec_ref(v___x_742_);
    return v_res_747_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(
    mut v___x_748_: *mut crate::leanh::LeanObject,
    mut v_x_749_: *mut crate::leanh::LeanObject,
    mut v_x_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_751_: u64 = 0;
    let mut v___x_752_: usize = 0;
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_750_);
    v___x_751_ =
        l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_748_, v_x_750_);
    v___x_752_ = lean_uint64_to_usize(v___x_751_);
    crate::leanh::lean_inc_ref(v_x_749_);
    v___x_753_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_748_, v_x_749_, v___x_752_, v_x_750_);
    return v___x_753_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg___boxed(
    mut v___x_754_: *mut crate::leanh::LeanObject,
    mut v_x_755_: *mut crate::leanh::LeanObject,
    mut v_x_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_754_, v_x_755_, v_x_756_);
    crate::leanh::lean_dec_ref(v_x_755_);
    crate::leanh::lean_dec_ref(v___x_754_);
    return v_res_757_;
}
pub unsafe fn l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
    mut v_a_758_: *mut crate::leanh::LeanObject,
    mut v_b_759_: *mut crate::leanh::LeanObject,
    mut v_a_760_: *mut crate::leanh::LeanObject,
    mut v_a_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
    mut v_a_763_: *mut crate::leanh::LeanObject,
    mut v_a_764_: *mut crate::leanh::LeanObject,
    mut v_a_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_779_: u8 = 0;
    let mut v_fst_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_785_: u8 = 0;
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_a_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_767_ = lean_st_ref_get(v_a_760_);
                v_toGoalState_768_ = crate::leanh::lean_ctor_get(v___x_767_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_768_);
                crate::leanh::lean_dec(v___x_767_);
                v_enodeMap_769_ = crate::leanh::lean_ctor_get(v_toGoalState_768_, 1);
                crate::leanh::lean_inc_ref(v_enodeMap_769_);
                v_congrTable_770_ = crate::leanh::lean_ctor_get(v_toGoalState_768_, 4);
                crate::leanh::lean_inc_ref(v_congrTable_770_);
                crate::leanh::lean_dec_ref(v_toGoalState_768_);
                v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq;
                v_key_772_ = l_Lean_mkAppB(v___x_771_, v_a_758_, v_b_759_);
                v___x_773_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v_enodeMap_769_, v_congrTable_770_, v_key_772_);
                crate::leanh::lean_dec_ref(v_congrTable_770_);
                crate::leanh::lean_dec_ref(v_enodeMap_769_);
                if crate::leanh::lean_obj_tag(v___x_773_) == 0 {
                    v___x_774_ = crate::leanh::lean_box(0);
                    v___x_775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
                    return v___x_775_;
                } else {
                    v_val_776_ = crate::leanh::lean_ctor_get(v___x_773_, 0);
                    v_isSharedCheck_806_ = (!crate::leanh::lean_is_exclusive(v___x_773_)) as u8;
                    if v_isSharedCheck_806_ == 0 {
                        v___x_778_ = v___x_773_;
                        v_isShared_779_ = v_isSharedCheck_806_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_776_);
                        crate::leanh::lean_dec(v___x_773_);
                        v___x_778_ = crate::leanh::lean_box(0);
                        v_isShared_779_ = v_isSharedCheck_806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_780_ = crate::leanh::lean_ctor_get(v_val_776_, 0);
                crate::leanh::lean_inc_n(v_fst_780_, 2);
                crate::leanh::lean_dec(v_val_776_);
                v___x_781_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                    v_fst_780_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_,
                );
                if crate::leanh::lean_obj_tag(v___x_781_) == 0 {
                    v_a_782_ = crate::leanh::lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_797_ = (!crate::leanh::lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_797_ == 0 {
                        v___x_784_ = v___x_781_;
                        v_isShared_785_ = v_isSharedCheck_797_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_782_);
                        crate::leanh::lean_dec(v___x_781_);
                        v___x_784_ = crate::leanh::lean_box(0);
                        v_isShared_785_ = v_isSharedCheck_797_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_780_);
                    crate::leanh::lean_del_object(v___x_778_);
                    v_a_798_ = crate::leanh::lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_805_ = (!crate::leanh::lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_805_ == 0 {
                        v___x_800_ = v___x_781_;
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_798_);
                        crate::leanh::lean_dec(v___x_781_);
                        v___x_800_ = crate::leanh::lean_box(0);
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_786_ = (crate::leanh::lean_unbox(v_a_782_) as u8);
                crate::leanh::lean_dec(v_a_782_);
                if v___x_786_ == 0 {
                    crate::leanh::lean_dec(v_fst_780_);
                    crate::leanh::lean_del_object(v___x_778_);
                    v___x_787_ = crate::leanh::lean_box(0);
                    if v_isShared_785_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_784_, 0, v___x_787_);
                        v___x_789_ = v___x_784_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_790_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
                        v___x_789_ = v_reuseFailAlloc_790_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_779_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_778_, 0, v_fst_780_);
                        v___x_792_ = v___x_778_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v_fst_780_);
                        v___x_792_ = v_reuseFailAlloc_796_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_789_;
            }
            4 => {
                if v_isShared_785_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_784_, 0, v___x_792_);
                    v___x_794_ = v___x_784_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
                    v___x_794_ = v_reuseFailAlloc_795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_794_;
            }
            6 => {
                if v_isShared_801_ == 0 {
                    v___x_803_ = v___x_800_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
                    v___x_803_ = v_reuseFailAlloc_804_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getDiseqFor_x3f___redArg___boxed(
    mut v_a_807_: *mut crate::leanh::LeanObject,
    mut v_b_808_: *mut crate::leanh::LeanObject,
    mut v_a_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
    mut v_a_811_: *mut crate::leanh::LeanObject,
    mut v_a_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v_a_814_: *mut crate::leanh::LeanObject,
    mut v_a_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
        v_a_807_, v_b_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_,
    );
    crate::leanh::lean_dec(v_a_814_);
    crate::leanh::lean_dec_ref(v_a_813_);
    crate::leanh::lean_dec(v_a_812_);
    crate::leanh::lean_dec_ref(v_a_811_);
    crate::leanh::lean_dec_ref(v_a_810_);
    crate::leanh::lean_dec(v_a_809_);
    return v_res_816_;
}
pub unsafe fn l_Lean_Meta_Grind_getDiseqFor_x3f(
    mut v_a_817_: *mut crate::leanh::LeanObject,
    mut v_b_818_: *mut crate::leanh::LeanObject,
    mut v_a_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
    mut v_a_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_830_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
        v_a_817_, v_b_818_, v_a_819_, v_a_823_, v_a_825_, v_a_826_, v_a_827_, v_a_828_,
    );
    return v___x_830_;
}
pub unsafe fn l_Lean_Meta_Grind_getDiseqFor_x3f___boxed(
    mut v_a_831_: *mut crate::leanh::LeanObject,
    mut v_b_832_: *mut crate::leanh::LeanObject,
    mut v_a_833_: *mut crate::leanh::LeanObject,
    mut v_a_834_: *mut crate::leanh::LeanObject,
    mut v_a_835_: *mut crate::leanh::LeanObject,
    mut v_a_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
    mut v_a_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Lean_Meta_Grind_getDiseqFor_x3f(
        v_a_831_, v_b_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_,
        v_a_840_, v_a_841_, v_a_842_,
    );
    crate::leanh::lean_dec(v_a_842_);
    crate::leanh::lean_dec_ref(v_a_841_);
    crate::leanh::lean_dec(v_a_840_);
    crate::leanh::lean_dec_ref(v_a_839_);
    crate::leanh::lean_dec(v_a_838_);
    crate::leanh::lean_dec_ref(v_a_837_);
    crate::leanh::lean_dec(v_a_836_);
    crate::leanh::lean_dec_ref(v_a_835_);
    crate::leanh::lean_dec(v_a_834_);
    crate::leanh::lean_dec(v_a_833_);
    return v_res_844_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(
    mut v___x_845_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_846_: *mut crate::leanh::LeanObject,
    mut v_x_847_: *mut crate::leanh::LeanObject,
    mut v_x_848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_845_, v_x_847_, v_x_848_);
    return v___x_849_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___boxed(
    mut v___x_850_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_851_: *mut crate::leanh::LeanObject,
    mut v_x_852_: *mut crate::leanh::LeanObject,
    mut v_x_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(
            v___x_850_,
            v_00_u03b2_851_,
            v_x_852_,
            v_x_853_,
        );
    crate::leanh::lean_dec_ref(v_x_852_);
    crate::leanh::lean_dec_ref(v___x_850_);
    return v_res_854_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(
    mut v___x_855_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_856_: *mut crate::leanh::LeanObject,
    mut v_x_857_: *mut crate::leanh::LeanObject,
    mut v_x_858_: usize,
    mut v_x_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_x_857_);
    v___x_860_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_855_, v_x_857_, v_x_858_, v_x_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___boxed(
    mut v___x_861_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_862_: *mut crate::leanh::LeanObject,
    mut v_x_863_: *mut crate::leanh::LeanObject,
    mut v_x_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4938__boxed_866_: usize = 0;
    let mut v_res_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4938__boxed_866_ = crate::leanh::lean_unbox_usize(v_x_864_);
    crate::leanh::lean_dec(v_x_864_);
    v_res_867_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(v___x_861_, v_00_u03b2_862_, v_x_863_, v_x_4938__boxed_866_, v_x_865_);
    crate::leanh::lean_dec_ref(v_x_863_);
    crate::leanh::lean_dec_ref(v___x_861_);
    return v_res_867_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(
    mut v___x_868_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_869_: *mut crate::leanh::LeanObject,
    mut v_keys_870_: *mut crate::leanh::LeanObject,
    mut v_vals_871_: *mut crate::leanh::LeanObject,
    mut v_heq_872_: *mut crate::leanh::LeanObject,
    mut v_i_873_: *mut crate::leanh::LeanObject,
    mut v_k_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_868_, v_keys_870_, v_vals_871_, v_i_873_, v_k_874_);
    return v___x_875_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___boxed(
    mut v___x_876_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_877_: *mut crate::leanh::LeanObject,
    mut v_keys_878_: *mut crate::leanh::LeanObject,
    mut v_vals_879_: *mut crate::leanh::LeanObject,
    mut v_heq_880_: *mut crate::leanh::LeanObject,
    mut v_i_881_: *mut crate::leanh::LeanObject,
    mut v_k_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(v___x_876_, v_00_u03b2_877_, v_keys_878_, v_vals_879_, v_heq_880_, v_i_881_, v_k_882_);
    crate::leanh::lean_dec_ref(v_vals_879_);
    crate::leanh::lean_dec_ref(v_keys_878_);
    crate::leanh::lean_dec_ref(v___x_876_);
    return v_res_883_;
}
pub unsafe fn l_Lean_Meta_Grind_isDiseq___redArg(
    mut v_a_884_: *mut crate::leanh::LeanObject,
    mut v_b_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
    mut v_a_888_: *mut crate::leanh::LeanObject,
    mut v_a_889_: *mut crate::leanh::LeanObject,
    mut v_a_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_a_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_893_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
                    v_a_884_, v_b_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_,
                );
                if crate::leanh::lean_obj_tag(v___x_893_) == 0 {
                    v_a_894_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                    v_isSharedCheck_908_ = (!crate::leanh::lean_is_exclusive(v___x_893_)) as u8;
                    if v_isSharedCheck_908_ == 0 {
                        v___x_896_ = v___x_893_;
                        v_isShared_897_ = v_isSharedCheck_908_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_894_);
                        crate::leanh::lean_dec(v___x_893_);
                        v___x_896_ = crate::leanh::lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_908_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_909_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                    v_isSharedCheck_916_ = (!crate::leanh::lean_is_exclusive(v___x_893_)) as u8;
                    if v_isSharedCheck_916_ == 0 {
                        v___x_911_ = v___x_893_;
                        v_isShared_912_ = v_isSharedCheck_916_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_909_);
                        crate::leanh::lean_dec(v___x_893_);
                        v___x_911_ = crate::leanh::lean_box(0);
                        v_isShared_912_ = v_isSharedCheck_916_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_894_) == 0 {
                    v___x_898_ = 0;
                    v___x_899_ = crate::leanh::lean_box((v___x_898_) as usize);
                    if v_isShared_897_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_899_);
                        v___x_901_ = v___x_896_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
                        v___x_901_ = v_reuseFailAlloc_902_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_894_, 1);
                    v___x_903_ = 1;
                    v___x_904_ = crate::leanh::lean_box((v___x_903_) as usize);
                    if v_isShared_897_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_904_);
                        v___x_906_ = v___x_896_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
                        v___x_906_ = v_reuseFailAlloc_907_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_901_;
            }
            3 => {
                return v___x_906_;
            }
            4 => {
                if v_isShared_912_ == 0 {
                    v___x_914_ = v___x_911_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
                    v___x_914_ = v_reuseFailAlloc_915_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_isDiseq___redArg___boxed(
    mut v_a_917_: *mut crate::leanh::LeanObject,
    mut v_b_918_: *mut crate::leanh::LeanObject,
    mut v_a_919_: *mut crate::leanh::LeanObject,
    mut v_a_920_: *mut crate::leanh::LeanObject,
    mut v_a_921_: *mut crate::leanh::LeanObject,
    mut v_a_922_: *mut crate::leanh::LeanObject,
    mut v_a_923_: *mut crate::leanh::LeanObject,
    mut v_a_924_: *mut crate::leanh::LeanObject,
    mut v_a_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_926_ = l_Lean_Meta_Grind_isDiseq___redArg(
        v_a_917_, v_b_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_,
    );
    crate::leanh::lean_dec(v_a_924_);
    crate::leanh::lean_dec_ref(v_a_923_);
    crate::leanh::lean_dec(v_a_922_);
    crate::leanh::lean_dec_ref(v_a_921_);
    crate::leanh::lean_dec_ref(v_a_920_);
    crate::leanh::lean_dec(v_a_919_);
    return v_res_926_;
}
pub unsafe fn l_Lean_Meta_Grind_isDiseq(
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_b_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
    mut v_a_932_: *mut crate::leanh::LeanObject,
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_a_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
    mut v_a_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = l_Lean_Meta_Grind_isDiseq___redArg(
        v_a_927_, v_b_928_, v_a_929_, v_a_933_, v_a_935_, v_a_936_, v_a_937_, v_a_938_,
    );
    return v___x_940_;
}
pub unsafe fn l_Lean_Meta_Grind_isDiseq___boxed(
    mut v_a_941_: *mut crate::leanh::LeanObject,
    mut v_b_942_: *mut crate::leanh::LeanObject,
    mut v_a_943_: *mut crate::leanh::LeanObject,
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_a_945_: *mut crate::leanh::LeanObject,
    mut v_a_946_: *mut crate::leanh::LeanObject,
    mut v_a_947_: *mut crate::leanh::LeanObject,
    mut v_a_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
    mut v_a_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lean_Meta_Grind_isDiseq(
        v_a_941_, v_b_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_,
        v_a_950_, v_a_951_, v_a_952_,
    );
    crate::leanh::lean_dec(v_a_952_);
    crate::leanh::lean_dec_ref(v_a_951_);
    crate::leanh::lean_dec(v_a_950_);
    crate::leanh::lean_dec_ref(v_a_949_);
    crate::leanh::lean_dec(v_a_948_);
    crate::leanh::lean_dec_ref(v_a_947_);
    crate::leanh::lean_dec(v_a_946_);
    crate::leanh::lean_dec_ref(v_a_945_);
    crate::leanh::lean_dec(v_a_944_);
    crate::leanh::lean_dec(v_a_943_);
    return v_res_954_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_955_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(
    mut v_msg_956_: *mut crate::leanh::LeanObject,
    mut v___y_957_: *mut crate::leanh::LeanObject,
    mut v___y_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12288__overap_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0,
    );
    v___x_12288__overap_969_ = lean_panic_fn_borrowed(v___x_968_, v_msg_956_);
    crate::leanh::lean_inc(v___y_966_);
    crate::leanh::lean_inc_ref(v___y_965_);
    crate::leanh::lean_inc(v___y_964_);
    crate::leanh::lean_inc_ref(v___y_963_);
    crate::leanh::lean_inc(v___y_962_);
    crate::leanh::lean_inc_ref(v___y_961_);
    crate::leanh::lean_inc(v___y_960_);
    crate::leanh::lean_inc_ref(v___y_959_);
    crate::leanh::lean_inc(v___y_958_);
    crate::leanh::lean_inc(v___y_957_);
    v___x_970_ = crate::leanh::lean_apply_11(
        v___x_12288__overap_969_,
        v___y_957_,
        v___y_958_,
        v___y_959_,
        v___y_960_,
        v___y_961_,
        v___y_962_,
        v___y_963_,
        v___y_964_,
        v___y_965_,
        v___y_966_,
        crate::leanh::lean_box(0),
    );
    return v___x_970_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___boxed(
    mut v_msg_971_: *mut crate::leanh::LeanObject,
    mut v___y_972_: *mut crate::leanh::LeanObject,
    mut v___y_973_: *mut crate::leanh::LeanObject,
    mut v___y_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
    mut v___y_976_: *mut crate::leanh::LeanObject,
    mut v___y_977_: *mut crate::leanh::LeanObject,
    mut v___y_978_: *mut crate::leanh::LeanObject,
    mut v___y_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_983_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(
        v_msg_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_,
        v___y_978_, v___y_979_, v___y_980_, v___y_981_,
    );
    crate::leanh::lean_dec(v___y_981_);
    crate::leanh::lean_dec_ref(v___y_980_);
    crate::leanh::lean_dec(v___y_979_);
    crate::leanh::lean_dec_ref(v___y_978_);
    crate::leanh::lean_dec(v___y_977_);
    crate::leanh::lean_dec_ref(v___y_976_);
    crate::leanh::lean_dec(v___y_975_);
    crate::leanh::lean_dec_ref(v___y_974_);
    crate::leanh::lean_dec(v___y_973_);
    crate::leanh::lean_dec(v___y_972_);
    return v_res_983_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2;
    v___x_988_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_989_ = crate::leanh::lean_unsigned_to_nat(44);
    v___x_990_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1;
    v___x_991_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0;
    v___x_992_ =
        l_mkPanicMessageWithDecl(v___x_991_, v___x_990_, v___x_989_, v___x_988_, v___x_987_);
    return v___x_992_;
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProofUsing(
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_b_1011_: *mut crate::leanh::LeanObject,
    mut v_eq_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
    mut v_a_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_a_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
    mut v_a_1019_: *mut crate::leanh::LeanObject,
    mut v_a_1020_: *mut crate::leanh::LeanObject,
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_a_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v_arg_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v_arg_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: u8 = 0;
    let mut v_arg_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: u8 = 0;
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v_u_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u8 = 0;
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1124_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_eq_1012_);
                v___x_1037_ = l_Lean_Expr_cleanupAnnotations(v_eq_1012_);
                v___x_1038_ = l_Lean_Expr_isApp(v___x_1037_);
                if v___x_1038_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1037_);
                    crate::leanh::lean_dec_ref(v_eq_1012_);
                    crate::leanh::lean_dec_ref(v_b_1011_);
                    crate::leanh::lean_dec_ref(v_a_1010_);
                    v___y_1025_ = v_a_1013_;
                    v___y_1026_ = v_a_1014_;
                    v___y_1027_ = v_a_1015_;
                    v___y_1028_ = v_a_1016_;
                    v___y_1029_ = v_a_1017_;
                    v___y_1030_ = v_a_1018_;
                    v___y_1031_ = v_a_1019_;
                    v___y_1032_ = v_a_1020_;
                    v___y_1033_ = v_a_1021_;
                    v___y_1034_ = v_a_1022_;
                    state = 1;
                    continue;
                } else {
                    v_arg_1039_ = crate::leanh::lean_ctor_get(v___x_1037_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1039_);
                    v___x_1040_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1037_);
                    v___x_1041_ = l_Lean_Expr_isApp(v___x_1040_);
                    if v___x_1041_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1040_);
                        crate::leanh::lean_dec_ref(v_arg_1039_);
                        crate::leanh::lean_dec_ref(v_eq_1012_);
                        crate::leanh::lean_dec_ref(v_b_1011_);
                        crate::leanh::lean_dec_ref(v_a_1010_);
                        v___y_1025_ = v_a_1013_;
                        v___y_1026_ = v_a_1014_;
                        v___y_1027_ = v_a_1015_;
                        v___y_1028_ = v_a_1016_;
                        v___y_1029_ = v_a_1017_;
                        v___y_1030_ = v_a_1018_;
                        v___y_1031_ = v_a_1019_;
                        v___y_1032_ = v_a_1020_;
                        v___y_1033_ = v_a_1021_;
                        v___y_1034_ = v_a_1022_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_1042_ = crate::leanh::lean_ctor_get(v___x_1040_, 1);
                        crate::leanh::lean_inc_ref(v_arg_1042_);
                        v___x_1043_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1040_);
                        v___x_1044_ = l_Lean_Expr_isApp(v___x_1043_);
                        if v___x_1044_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1043_);
                            crate::leanh::lean_dec_ref(v_arg_1042_);
                            crate::leanh::lean_dec_ref(v_arg_1039_);
                            crate::leanh::lean_dec_ref(v_eq_1012_);
                            crate::leanh::lean_dec_ref(v_b_1011_);
                            crate::leanh::lean_dec_ref(v_a_1010_);
                            v___y_1025_ = v_a_1013_;
                            v___y_1026_ = v_a_1014_;
                            v___y_1027_ = v_a_1015_;
                            v___y_1028_ = v_a_1016_;
                            v___y_1029_ = v_a_1017_;
                            v___y_1030_ = v_a_1018_;
                            v___y_1031_ = v_a_1019_;
                            v___y_1032_ = v_a_1020_;
                            v___y_1033_ = v_a_1021_;
                            v___y_1034_ = v_a_1022_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_1045_ = crate::leanh::lean_ctor_get(v___x_1043_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1045_);
                            v___x_1046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1043_);
                            v___x_1047_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1;
                            v___x_1048_ = l_Lean_Expr_isConstOf(v___x_1046_, v___x_1047_);
                            if v___x_1048_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1046_);
                                crate::leanh::lean_dec_ref(v_arg_1045_);
                                crate::leanh::lean_dec_ref(v_arg_1042_);
                                crate::leanh::lean_dec_ref(v_arg_1039_);
                                crate::leanh::lean_dec_ref(v_eq_1012_);
                                crate::leanh::lean_dec_ref(v_b_1011_);
                                crate::leanh::lean_dec_ref(v_a_1010_);
                                v___y_1025_ = v_a_1013_;
                                v___y_1026_ = v_a_1014_;
                                v___y_1027_ = v_a_1015_;
                                v___y_1028_ = v_a_1016_;
                                v___y_1029_ = v_a_1017_;
                                v___y_1030_ = v_a_1018_;
                                v___y_1031_ = v_a_1019_;
                                v___y_1032_ = v_a_1020_;
                                v___y_1033_ = v_a_1021_;
                                v___y_1034_ = v_a_1022_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_eq_1012_);
                                v___x_1049_ = l_Lean_Meta_Grind_mkEqFalseProof(
                                    v_eq_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_,
                                    v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_,
                                    v_a_1022_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1049_) == 0 {
                                    v_a_1050_ = crate::leanh::lean_ctor_get(v___x_1049_, 0);
                                    v_isSharedCheck_1124_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1049_)) as u8;
                                    if v_isSharedCheck_1124_ == 0 {
                                        v___x_1052_ = v___x_1049_;
                                        v_isShared_1053_ = v_isSharedCheck_1124_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1050_);
                                        crate::leanh::lean_dec(v___x_1049_);
                                        v___x_1052_ = crate::leanh::lean_box(0);
                                        v_isShared_1053_ = v_isSharedCheck_1124_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1046_);
                                    crate::leanh::lean_dec_ref(v_arg_1045_);
                                    crate::leanh::lean_dec_ref(v_arg_1042_);
                                    crate::leanh::lean_dec_ref(v_arg_1039_);
                                    crate::leanh::lean_dec_ref(v_eq_1012_);
                                    crate::leanh::lean_dec_ref(v_b_1011_);
                                    crate::leanh::lean_dec_ref(v_a_1010_);
                                    return v___x_1049_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1035_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3_once),
                    _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3,
                );
                v___x_1036_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(
                    v___x_1035_,
                    v___y_1025_,
                    v___y_1026_,
                    v___y_1027_,
                    v___y_1028_,
                    v___y_1029_,
                    v___y_1030_,
                    v___y_1031_,
                    v___y_1032_,
                    v___y_1033_,
                    v___y_1034_,
                );
                return v___x_1036_;
            }
            2 => {
                v_u_1054_ = l_Lean_Expr_constLevels_x21(v___x_1046_);
                crate::leanh::lean_dec_ref(v___x_1046_);
                v___x_1104_ = l_Lean_Meta_mkOfEqFalseCore(v_eq_1012_, v_a_1050_);
                v___x_1120_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1010_, v_arg_1042_, v_a_1013_);
                if crate::leanh::lean_obj_tag(v___x_1120_) == 0 {
                    v_a_1121_ = crate::leanh::lean_ctor_get(v___x_1120_, 0);
                    crate::leanh::lean_inc(v_a_1121_);
                    v___x_1122_ = (crate::leanh::lean_unbox(v_a_1121_) as u8);
                    crate::leanh::lean_dec(v_a_1121_);
                    if v___x_1122_ == 0 {
                        v___y_1106_ = v___x_1120_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1120_, 1);
                        v___x_1123_ =
                            l_Lean_Meta_Grind_isEqv___redArg(v_b_1011_, v_arg_1039_, v_a_1013_);
                        v___y_1106_ = v___x_1123_;
                        state = 8;
                        continue;
                    }
                } else {
                    v___y_1106_ = v___x_1120_;
                    state = 8;
                    continue;
                }
            }
            3 => {
                v___x_1068_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_b_1011_,
                        v___y_1056_,
                    );
                if v___x_1068_ == 0 {
                    crate::leanh::lean_del_object(v___x_1052_);
                    crate::leanh::lean_inc(v___y_1067_);
                    crate::leanh::lean_inc_ref(v___y_1066_);
                    crate::leanh::lean_inc(v___y_1065_);
                    crate::leanh::lean_inc_ref(v___y_1064_);
                    crate::leanh::lean_inc(v___y_1063_);
                    crate::leanh::lean_inc_ref(v___y_1062_);
                    crate::leanh::lean_inc(v___y_1061_);
                    crate::leanh::lean_inc_ref(v___y_1060_);
                    crate::leanh::lean_inc(v___y_1059_);
                    crate::leanh::lean_inc(v___y_1058_);
                    crate::leanh::lean_inc_ref(v___y_1056_);
                    crate::leanh::lean_inc_ref(v_b_1011_);
                    v___x_1069_ = lean_grind_mk_eq_proof(
                        v_b_1011_,
                        v___y_1056_,
                        v___y_1058_,
                        v___y_1059_,
                        v___y_1060_,
                        v___y_1061_,
                        v___y_1062_,
                        v___y_1063_,
                        v___y_1064_,
                        v___y_1065_,
                        v___y_1066_,
                        v___y_1067_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1069_) == 0 {
                        v_a_1070_ = crate::leanh::lean_ctor_get(v___x_1069_, 0);
                        v_isSharedCheck_1080_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1069_)) as u8;
                        if v_isSharedCheck_1080_ == 0 {
                            v___x_1072_ = v___x_1069_;
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1070_);
                            crate::leanh::lean_dec(v___x_1069_);
                            v___x_1072_ = crate::leanh::lean_box(0);
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_h_1057_);
                        crate::leanh::lean_dec_ref(v___y_1056_);
                        crate::leanh::lean_dec(v_u_1054_);
                        crate::leanh::lean_dec_ref(v_arg_1045_);
                        crate::leanh::lean_dec_ref(v_b_1011_);
                        crate::leanh::lean_dec_ref(v_a_1010_);
                        return v___x_1069_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1056_);
                    crate::leanh::lean_dec(v_u_1054_);
                    crate::leanh::lean_dec_ref(v_arg_1045_);
                    crate::leanh::lean_dec_ref(v_b_1011_);
                    crate::leanh::lean_dec_ref(v_a_1010_);
                    if v_isShared_1053_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1052_, 0, v_h_1057_);
                        v___x_1082_ = v___x_1052_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1083_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_h_1057_);
                        v___x_1082_ = v_reuseFailAlloc_1083_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1074_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7;
                v___x_1075_ = l_Lean_mkConst(v___x_1074_, v_u_1054_);
                v___x_1076_ = l_Lean_mkApp6(
                    v___x_1075_,
                    v_arg_1045_,
                    v_b_1011_,
                    v_a_1010_,
                    v___y_1056_,
                    v_a_1070_,
                    v_h_1057_,
                );
                if v_isShared_1073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1076_);
                    v___x_1078_ = v___x_1072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
                    v___x_1078_ = v_reuseFailAlloc_1079_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1078_;
            }
            6 => {
                return v___x_1082_;
            }
            7 => {
                v___x_1098_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_a_1010_,
                        v_fst_1085_,
                    );
                if v___x_1098_ == 0 {
                    crate::leanh::lean_inc(v___y_1097_);
                    crate::leanh::lean_inc_ref(v___y_1096_);
                    crate::leanh::lean_inc(v___y_1095_);
                    crate::leanh::lean_inc_ref(v___y_1094_);
                    crate::leanh::lean_inc(v___y_1093_);
                    crate::leanh::lean_inc_ref(v___y_1092_);
                    crate::leanh::lean_inc(v___y_1091_);
                    crate::leanh::lean_inc_ref(v___y_1090_);
                    crate::leanh::lean_inc(v___y_1089_);
                    crate::leanh::lean_inc(v___y_1088_);
                    crate::leanh::lean_inc_ref(v_fst_1085_);
                    crate::leanh::lean_inc_ref(v_a_1010_);
                    v___x_1099_ = lean_grind_mk_eq_proof(
                        v_a_1010_,
                        v_fst_1085_,
                        v___y_1088_,
                        v___y_1089_,
                        v___y_1090_,
                        v___y_1091_,
                        v___y_1092_,
                        v___y_1093_,
                        v___y_1094_,
                        v___y_1095_,
                        v___y_1096_,
                        v___y_1097_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1099_) == 0 {
                        v_a_1100_ = crate::leanh::lean_ctor_get(v___x_1099_, 0);
                        crate::leanh::lean_inc(v_a_1100_);
                        crate::leanh::lean_dec_ref_known(v___x_1099_, 1);
                        v___x_1101_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9;
                        crate::leanh::lean_inc(v_u_1054_);
                        v___x_1102_ = l_Lean_mkConst(v___x_1101_, v_u_1054_);
                        crate::leanh::lean_inc_ref(v_fst_1086_);
                        crate::leanh::lean_inc_ref(v_a_1010_);
                        crate::leanh::lean_inc_ref(v_arg_1045_);
                        v___x_1103_ = l_Lean_mkApp6(
                            v___x_1102_,
                            v_arg_1045_,
                            v_a_1010_,
                            v_fst_1085_,
                            v_fst_1086_,
                            v_a_1100_,
                            v_snd_1087_,
                        );
                        v___y_1056_ = v_fst_1086_;
                        v_h_1057_ = v___x_1103_;
                        v___y_1058_ = v___y_1088_;
                        v___y_1059_ = v___y_1089_;
                        v___y_1060_ = v___y_1090_;
                        v___y_1061_ = v___y_1091_;
                        v___y_1062_ = v___y_1092_;
                        v___y_1063_ = v___y_1093_;
                        v___y_1064_ = v___y_1094_;
                        v___y_1065_ = v___y_1095_;
                        v___y_1066_ = v___y_1096_;
                        v___y_1067_ = v___y_1097_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_snd_1087_);
                        crate::leanh::lean_dec_ref(v_fst_1086_);
                        crate::leanh::lean_dec_ref(v_fst_1085_);
                        crate::leanh::lean_dec(v_u_1054_);
                        crate::leanh::lean_del_object(v___x_1052_);
                        crate::leanh::lean_dec_ref(v_arg_1045_);
                        crate::leanh::lean_dec_ref(v_b_1011_);
                        crate::leanh::lean_dec_ref(v_a_1010_);
                        return v___x_1099_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fst_1085_);
                    v___y_1056_ = v_fst_1086_;
                    v_h_1057_ = v_snd_1087_;
                    v___y_1058_ = v___y_1088_;
                    v___y_1059_ = v___y_1089_;
                    v___y_1060_ = v___y_1090_;
                    v___y_1061_ = v___y_1091_;
                    v___y_1062_ = v___y_1092_;
                    v___y_1063_ = v___y_1093_;
                    v___y_1064_ = v___y_1094_;
                    v___y_1065_ = v___y_1095_;
                    v___y_1066_ = v___y_1096_;
                    v___y_1067_ = v___y_1097_;
                    state = 3;
                    continue;
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_1106_) == 0 {
                    v_a_1107_ = crate::leanh::lean_ctor_get(v___y_1106_, 0);
                    crate::leanh::lean_inc(v_a_1107_);
                    crate::leanh::lean_dec_ref_known(v___y_1106_, 1);
                    v___x_1108_ = (crate::leanh::lean_unbox(v_a_1107_) as u8);
                    crate::leanh::lean_dec(v_a_1107_);
                    if v___x_1108_ == 0 {
                        v___x_1109_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12;
                        crate::leanh::lean_inc(v_u_1054_);
                        v___x_1110_ = l_Lean_mkConst(v___x_1109_, v_u_1054_);
                        crate::leanh::lean_inc_ref(v_arg_1039_);
                        crate::leanh::lean_inc_ref(v_arg_1042_);
                        crate::leanh::lean_inc_ref(v_arg_1045_);
                        v___x_1111_ = l_Lean_mkApp4(
                            v___x_1110_,
                            v_arg_1045_,
                            v_arg_1042_,
                            v_arg_1039_,
                            v___x_1104_,
                        );
                        v_fst_1085_ = v_arg_1039_;
                        v_fst_1086_ = v_arg_1042_;
                        v_snd_1087_ = v___x_1111_;
                        v___y_1088_ = v_a_1013_;
                        v___y_1089_ = v_a_1014_;
                        v___y_1090_ = v_a_1015_;
                        v___y_1091_ = v_a_1016_;
                        v___y_1092_ = v_a_1017_;
                        v___y_1093_ = v_a_1018_;
                        v___y_1094_ = v_a_1019_;
                        v___y_1095_ = v_a_1020_;
                        v___y_1096_ = v_a_1021_;
                        v___y_1097_ = v_a_1022_;
                        state = 7;
                        continue;
                    } else {
                        v_fst_1085_ = v_arg_1042_;
                        v_fst_1086_ = v_arg_1039_;
                        v_snd_1087_ = v___x_1104_;
                        v___y_1088_ = v_a_1013_;
                        v___y_1089_ = v_a_1014_;
                        v___y_1090_ = v_a_1015_;
                        v___y_1091_ = v_a_1016_;
                        v___y_1092_ = v_a_1017_;
                        v___y_1093_ = v_a_1018_;
                        v___y_1094_ = v_a_1019_;
                        v___y_1095_ = v_a_1020_;
                        v___y_1096_ = v_a_1021_;
                        v___y_1097_ = v_a_1022_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1104_);
                    crate::leanh::lean_dec(v_u_1054_);
                    crate::leanh::lean_del_object(v___x_1052_);
                    crate::leanh::lean_dec_ref(v_arg_1045_);
                    crate::leanh::lean_dec_ref(v_arg_1042_);
                    crate::leanh::lean_dec_ref(v_arg_1039_);
                    crate::leanh::lean_dec_ref(v_b_1011_);
                    crate::leanh::lean_dec_ref(v_a_1010_);
                    v_a_1112_ = crate::leanh::lean_ctor_get(v___y_1106_, 0);
                    v_isSharedCheck_1119_ = (!crate::leanh::lean_is_exclusive(v___y_1106_)) as u8;
                    if v_isSharedCheck_1119_ == 0 {
                        v___x_1114_ = v___y_1106_;
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1112_);
                        crate::leanh::lean_dec(v___y_1106_);
                        v___x_1114_ = crate::leanh::lean_box(0);
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_1115_ == 0 {
                    v___x_1117_ = v___x_1114_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
                    v___x_1117_ = v_reuseFailAlloc_1118_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1117_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProofUsing___boxed(
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_b_1126_: *mut crate::leanh::LeanObject,
    mut v_eq_1127_: *mut crate::leanh::LeanObject,
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_a_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
    mut v_a_1137_: *mut crate::leanh::LeanObject,
    mut v_a_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1139_ = l_Lean_Meta_Grind_mkDiseqProofUsing(
        v_a_1125_, v_b_1126_, v_eq_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_,
        v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_,
    );
    crate::leanh::lean_dec(v_a_1137_);
    crate::leanh::lean_dec_ref(v_a_1136_);
    crate::leanh::lean_dec(v_a_1135_);
    crate::leanh::lean_dec_ref(v_a_1134_);
    crate::leanh::lean_dec(v_a_1133_);
    crate::leanh::lean_dec_ref(v_a_1132_);
    crate::leanh::lean_dec(v_a_1131_);
    crate::leanh::lean_dec_ref(v_a_1130_);
    crate::leanh::lean_dec(v_a_1129_);
    crate::leanh::lean_dec(v_a_1128_);
    return v_res_1139_;
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProof_x3f(
    mut v_a_1140_: *mut crate::leanh::LeanObject,
    mut v_b_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
    mut v_a_1143_: *mut crate::leanh::LeanObject,
    mut v_a_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
    mut v_a_1148_: *mut crate::leanh::LeanObject,
    mut v_a_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v_val_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v_a_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_b_1141_);
                crate::leanh::lean_inc_ref(v_a_1140_);
                v___x_1153_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
                    v_a_1140_, v_b_1141_, v_a_1142_, v_a_1146_, v_a_1148_, v_a_1149_, v_a_1150_,
                    v_a_1151_,
                );
                if crate::leanh::lean_obj_tag(v___x_1153_) == 0 {
                    v_a_1154_ = crate::leanh::lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1187_ = (!crate::leanh::lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1187_ == 0 {
                        v___x_1156_ = v___x_1153_;
                        v_isShared_1157_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1154_);
                        crate::leanh::lean_dec(v___x_1153_);
                        v___x_1156_ = crate::leanh::lean_box(0);
                        v_isShared_1157_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1141_);
                    crate::leanh::lean_dec_ref(v_a_1140_);
                    return v___x_1153_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1154_) == 1 {
                    crate::leanh::lean_del_object(v___x_1156_);
                    v_val_1158_ = crate::leanh::lean_ctor_get(v_a_1154_, 0);
                    v_isSharedCheck_1182_ = (!crate::leanh::lean_is_exclusive(v_a_1154_)) as u8;
                    if v_isSharedCheck_1182_ == 0 {
                        v___x_1160_ = v_a_1154_;
                        v_isShared_1161_ = v_isSharedCheck_1182_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1158_);
                        crate::leanh::lean_dec(v_a_1154_);
                        v___x_1160_ = crate::leanh::lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1182_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1154_);
                    crate::leanh::lean_dec_ref(v_b_1141_);
                    crate::leanh::lean_dec_ref(v_a_1140_);
                    v___x_1183_ = crate::leanh::lean_box(0);
                    if v_isShared_1157_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1156_, 0, v___x_1183_);
                        v___x_1185_ = v___x_1156_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
                        v___x_1185_ = v_reuseFailAlloc_1186_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1162_ = l_Lean_Meta_Grind_mkDiseqProofUsing(
                    v_a_1140_,
                    v_b_1141_,
                    v_val_1158_,
                    v_a_1142_,
                    v_a_1143_,
                    v_a_1144_,
                    v_a_1145_,
                    v_a_1146_,
                    v_a_1147_,
                    v_a_1148_,
                    v_a_1149_,
                    v_a_1150_,
                    v_a_1151_,
                );
                if crate::leanh::lean_obj_tag(v___x_1162_) == 0 {
                    v_a_1163_ = crate::leanh::lean_ctor_get(v___x_1162_, 0);
                    v_isSharedCheck_1173_ = (!crate::leanh::lean_is_exclusive(v___x_1162_)) as u8;
                    if v_isSharedCheck_1173_ == 0 {
                        v___x_1165_ = v___x_1162_;
                        v_isShared_1166_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1163_);
                        crate::leanh::lean_dec(v___x_1162_);
                        v___x_1165_ = crate::leanh::lean_box(0);
                        v_isShared_1166_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1160_);
                    v_a_1174_ = crate::leanh::lean_ctor_get(v___x_1162_, 0);
                    v_isSharedCheck_1181_ = (!crate::leanh::lean_is_exclusive(v___x_1162_)) as u8;
                    if v_isSharedCheck_1181_ == 0 {
                        v___x_1176_ = v___x_1162_;
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1174_);
                        crate::leanh::lean_dec(v___x_1162_);
                        v___x_1176_ = crate::leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1161_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1160_, 0, v_a_1163_);
                    v___x_1168_ = v___x_1160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1163_);
                    v___x_1168_ = v_reuseFailAlloc_1172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1166_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1165_, 0, v___x_1168_);
                    v___x_1170_ = v___x_1165_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
                    v___x_1170_ = v_reuseFailAlloc_1171_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1170_;
            }
            6 => {
                if v_isShared_1177_ == 0 {
                    v___x_1179_ = v___x_1176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1179_;
            }
            8 => {
                return v___x_1185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProof_x3f___boxed(
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_b_1189_: *mut crate::leanh::LeanObject,
    mut v_a_1190_: *mut crate::leanh::LeanObject,
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(
        v_a_1188_, v_b_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_,
        v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_,
    );
    crate::leanh::lean_dec(v_a_1199_);
    crate::leanh::lean_dec_ref(v_a_1198_);
    crate::leanh::lean_dec(v_a_1197_);
    crate::leanh::lean_dec_ref(v_a_1196_);
    crate::leanh::lean_dec(v_a_1195_);
    crate::leanh::lean_dec_ref(v_a_1194_);
    crate::leanh::lean_dec(v_a_1193_);
    crate::leanh::lean_dec_ref(v_a_1192_);
    crate::leanh::lean_dec(v_a_1191_);
    crate::leanh::lean_dec(v_a_1190_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(
    mut v_msgData_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = lean_st_ref_get(v___y_1206_);
    v_env_1209_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
    crate::leanh::lean_inc_ref(v_env_1209_);
    crate::leanh::lean_dec(v___x_1208_);
    v___x_1210_ = lean_st_ref_get(v___y_1204_);
    v_mctx_1211_ = crate::leanh::lean_ctor_get(v___x_1210_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1211_);
    crate::leanh::lean_dec(v___x_1210_);
    v_lctx_1212_ = crate::leanh::lean_ctor_get(v___y_1203_, 2);
    v_options_1213_ = crate::leanh::lean_ctor_get(v___y_1205_, 2);
    crate::leanh::lean_inc_ref(v_options_1213_);
    crate::leanh::lean_inc_ref(v_lctx_1212_);
    v___x_1214_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1214_, 0, v_env_1209_);
    crate::leanh::lean_ctor_set(v___x_1214_, 1, v_mctx_1211_);
    crate::leanh::lean_ctor_set(v___x_1214_, 2, v_lctx_1212_);
    crate::leanh::lean_ctor_set(v___x_1214_, 3, v_options_1213_);
    v___x_1215_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
    crate::leanh::lean_ctor_set(v___x_1215_, 1, v_msgData_1202_);
    v___x_1216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1216_, 0, v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0___boxed(
    mut v_msgData_1217_: *mut crate::leanh::LeanObject,
    mut v___y_1218_: *mut crate::leanh::LeanObject,
    mut v___y_1219_: *mut crate::leanh::LeanObject,
    mut v___y_1220_: *mut crate::leanh::LeanObject,
    mut v___y_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1223_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msgData_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
    crate::leanh::lean_dec(v___y_1221_);
    crate::leanh::lean_dec_ref(v___y_1220_);
    crate::leanh::lean_dec(v___y_1219_);
    crate::leanh::lean_dec_ref(v___y_1218_);
    return v_res_1223_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(
    mut v_msg_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
    mut v___y_1227_: *mut crate::leanh::LeanObject,
    mut v___y_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1230_ = crate::leanh::lean_ctor_get(v___y_1227_, 5);
                v___x_1231_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msg_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
                v_a_1232_ = crate::leanh::lean_ctor_get(v___x_1231_, 0);
                v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v___x_1231_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v___x_1234_ = v___x_1231_;
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1232_);
                    crate::leanh::lean_dec(v___x_1231_);
                    v___x_1234_ = crate::leanh::lean_box(0);
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1230_);
                v___x_1236_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1236_, 0, v_ref_1230_);
                crate::leanh::lean_ctor_set(v___x_1236_, 1, v_a_1232_);
                if v_isShared_1235_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1234_, 1);
                    crate::leanh::lean_ctor_set(v___x_1234_, 0, v___x_1236_);
                    v___x_1238_ = v___x_1234_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
                    v___x_1238_ = v_reuseFailAlloc_1239_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg___boxed(
    mut v_msg_1241_: *mut crate::leanh::LeanObject,
    mut v___y_1242_: *mut crate::leanh::LeanObject,
    mut v___y_1243_: *mut crate::leanh::LeanObject,
    mut v___y_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1247_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(
        v_msg_1241_,
        v___y_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
    );
    crate::leanh::lean_dec(v___y_1245_);
    crate::leanh::lean_dec_ref(v___y_1244_);
    crate::leanh::lean_dec(v___y_1243_);
    crate::leanh::lean_dec_ref(v___y_1242_);
    return v_res_1247_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l_Lean_Meta_Grind_mkDiseqProof___closed__0;
    v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lean_Meta_Grind_mkDiseqProof___closed__2;
    v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProof(
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_b_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
    mut v_a_1257_: *mut crate::leanh::LeanObject,
    mut v_a_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
    mut v_a_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v_val_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_a_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_b_1255_);
                crate::leanh::lean_inc_ref(v_a_1254_);
                v___x_1267_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(
                    v_a_1254_, v_b_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_,
                    v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_,
                );
                if crate::leanh::lean_obj_tag(v___x_1267_) == 0 {
                    v_a_1268_ = crate::leanh::lean_ctor_get(v___x_1267_, 0);
                    v_isSharedCheck_1284_ = (!crate::leanh::lean_is_exclusive(v___x_1267_)) as u8;
                    if v_isSharedCheck_1284_ == 0 {
                        v___x_1270_ = v___x_1267_;
                        v_isShared_1271_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1268_);
                        crate::leanh::lean_dec(v___x_1267_);
                        v___x_1270_ = crate::leanh::lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_1255_);
                    crate::leanh::lean_dec_ref(v_a_1254_);
                    v_a_1285_ = crate::leanh::lean_ctor_get(v___x_1267_, 0);
                    v_isSharedCheck_1292_ = (!crate::leanh::lean_is_exclusive(v___x_1267_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1287_ = v___x_1267_;
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1285_);
                        crate::leanh::lean_dec(v___x_1267_);
                        v___x_1287_ = crate::leanh::lean_box(0);
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1268_) == 1 {
                    crate::leanh::lean_dec_ref(v_b_1255_);
                    crate::leanh::lean_dec_ref(v_a_1254_);
                    v_val_1272_ = crate::leanh::lean_ctor_get(v_a_1268_, 0);
                    crate::leanh::lean_inc(v_val_1272_);
                    crate::leanh::lean_dec_ref_known(v_a_1268_, 1);
                    if v_isShared_1271_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1270_, 0, v_val_1272_);
                        v___x_1274_ = v___x_1270_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_val_1272_);
                        v___x_1274_ = v_reuseFailAlloc_1275_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1270_);
                    crate::leanh::lean_dec(v_a_1268_);
                    v___x_1276_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__1_once),
                        _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1,
                    );
                    v___x_1277_ = l_Lean_indentExpr(v_a_1254_);
                    v___x_1278_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1278_, 0, v___x_1276_);
                    crate::leanh::lean_ctor_set(v___x_1278_, 1, v___x_1277_);
                    v___x_1279_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__3_once),
                        _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3,
                    );
                    v___x_1280_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1280_, 0, v___x_1278_);
                    crate::leanh::lean_ctor_set(v___x_1280_, 1, v___x_1279_);
                    v___x_1281_ = l_Lean_indentExpr(v_b_1255_);
                    v___x_1282_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1282_, 0, v___x_1280_);
                    crate::leanh::lean_ctor_set(v___x_1282_, 1, v___x_1281_);
                    v___x_1283_ =
                        l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(
                            v___x_1282_,
                            v_a_1262_,
                            v_a_1263_,
                            v_a_1264_,
                            v_a_1265_,
                        );
                    return v___x_1283_;
                }
            }
            2 => {
                return v___x_1274_;
            }
            3 => {
                if v_isShared_1288_ == 0 {
                    v___x_1290_ = v___x_1287_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
                    v___x_1290_ = v_reuseFailAlloc_1291_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1290_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProof___boxed(
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_b_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
    mut v_a_1296_: *mut crate::leanh::LeanObject,
    mut v_a_1297_: *mut crate::leanh::LeanObject,
    mut v_a_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
    mut v_a_1302_: *mut crate::leanh::LeanObject,
    mut v_a_1303_: *mut crate::leanh::LeanObject,
    mut v_a_1304_: *mut crate::leanh::LeanObject,
    mut v_a_1305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Lean_Meta_Grind_mkDiseqProof(
        v_a_1293_, v_b_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_,
        v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_,
    );
    crate::leanh::lean_dec(v_a_1304_);
    crate::leanh::lean_dec_ref(v_a_1303_);
    crate::leanh::lean_dec(v_a_1302_);
    crate::leanh::lean_dec_ref(v_a_1301_);
    crate::leanh::lean_dec(v_a_1300_);
    crate::leanh::lean_dec_ref(v_a_1299_);
    crate::leanh::lean_dec(v_a_1298_);
    crate::leanh::lean_dec_ref(v_a_1297_);
    crate::leanh::lean_dec(v_a_1296_);
    crate::leanh::lean_dec(v_a_1295_);
    return v_res_1306_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(
    mut v_00_u03b1_1307_: *mut crate::leanh::LeanObject,
    mut v_msg_1308_: *mut crate::leanh::LeanObject,
    mut v___y_1309_: *mut crate::leanh::LeanObject,
    mut v___y_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
    mut v___y_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1320_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(
        v_msg_1308_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
        v___y_1318_,
    );
    return v___x_1320_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___boxed(
    mut v_00_u03b1_1321_: *mut crate::leanh::LeanObject,
    mut v_msg_1322_: *mut crate::leanh::LeanObject,
    mut v___y_1323_: *mut crate::leanh::LeanObject,
    mut v___y_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
    mut v___y_1332_: *mut crate::leanh::LeanObject,
    mut v___y_1333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1334_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(
        v_00_u03b1_1321_,
        v_msg_1322_,
        v___y_1323_,
        v___y_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
        v___y_1329_,
        v___y_1330_,
        v___y_1331_,
        v___y_1332_,
    );
    crate::leanh::lean_dec(v___y_1332_);
    crate::leanh::lean_dec_ref(v___y_1331_);
    crate::leanh::lean_dec(v___y_1330_);
    crate::leanh::lean_dec_ref(v___y_1329_);
    crate::leanh::lean_dec(v___y_1328_);
    crate::leanh::lean_dec_ref(v___y_1327_);
    crate::leanh::lean_dec(v___y_1326_);
    crate::leanh::lean_dec_ref(v___y_1325_);
    crate::leanh::lean_dec(v___y_1324_);
    crate::leanh::lean_dec(v___y_1323_);
    return v_res_1334_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq =
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Diseq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Diseq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
}
