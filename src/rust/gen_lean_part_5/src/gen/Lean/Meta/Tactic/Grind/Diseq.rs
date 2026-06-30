// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Diseq
// Imports: Lean.Meta.Tactic.Grind.Types Init.Grind.Lemmas
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_grind_mk_eq_proof,
    lean_nat_add, lean_nat_dec_lt, lean_panic_fn_borrowed, lean_st_ref_get, lean_uint64_to_usize,
    lean_usize_land, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
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
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value:
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
    m_data: [69, 113, 0],
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1_value:
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
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__0_value
        ) as *mut leanh::LeanObject,
        16122875713692181903 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value:
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
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6_value:
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
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__5_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0_value: leanh::LeanStringObject<
    29,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 109, 107, 68, 105,
        115, 101, 113, 80, 114, 111, 111, 102, 85, 115, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value: leanh::LeanStringObject<
    21,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__6_value)
                as *mut leanh::LeanObject,
            15085210600211958602 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value: leanh::LeanStringObject<
    20,
> = leanh::LeanStringObject {
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
        110, 101, 95, 111, 102, 95, 110, 101, 95, 111, 102, 95, 101, 113, 95, 108, 101, 102, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__4_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__5_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__8_value)
                as *mut leanh::LeanObject,
            12081245626925201571 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value: leanh::LeanStringObject<
    3,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__10_value)
            as *mut leanh::LeanObject,
        6695605208187598753 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__11_value)
                as *mut leanh::LeanObject,
            6773482220982667626 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_mkDiseqProof___closed__0_value: leanh::LeanStringObject<62> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProof___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_mkDiseqProof___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_mkDiseqProof___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_mkDiseqProof___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = leanh::lean_unsigned_to_nat(1);
    v___x_672_ = l_Lean_Level_ofNat(v___x_671_);
    return v___x_672_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = leanh::lean_box(0);
    v___x_674_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__2,
    );
    v___x_675_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_675_, 0, v___x_674_);
    leanh::lean_ctor_set(v___x_675_, 1, v___x_673_);
    return v___x_675_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_682_ = leanh::lean_box(0);
    v___x_683_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__6;
    v___x_684_ = l_Lean_Expr_const___override(v___x_683_, v___x_682_);
    return v___x_684_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7_once
        ),
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__7,
    );
    v___x_686_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ = leanh::lean_obj_once(
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
    mut v___x_689_: *mut leanh::LeanObject,
    mut v_keys_690_: *mut leanh::LeanObject,
    mut v_vals_691_: *mut leanh::LeanObject,
    mut v_i_692_: *mut leanh::LeanObject,
    mut v_k_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_694_ = lean_array_get_size(v_keys_690_);
                v___x_695_ = lean_nat_dec_lt(v_i_692_, v___x_694_);
                if v___x_695_ == 0 {
                    leanh::lean_dec_ref(v_k_693_);
                    leanh::lean_dec(v_i_692_);
                    v___x_696_ = leanh::lean_box(0);
                    return v___x_696_;
                } else {
                    v_k_x27_697_ = lean_array_fget_borrowed(v_keys_690_, v_i_692_);
                    leanh::lean_inc(v_k_x27_697_);
                    leanh::lean_inc_ref(v_k_693_);
                    v___x_698_ =
                        l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(
                            v___x_689_,
                            v_k_693_,
                            v_k_x27_697_,
                        );
                    if v___x_698_ == 0 {
                        v___x_699_ = leanh::lean_unsigned_to_nat(1);
                        v___x_700_ = lean_nat_add(v_i_692_, v___x_699_);
                        leanh::lean_dec(v_i_692_);
                        v_i_692_ = v___x_700_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_k_693_);
                        v___x_702_ = lean_array_fget_borrowed(v_vals_691_, v_i_692_);
                        leanh::lean_dec(v_i_692_);
                        leanh::lean_inc(v___x_702_);
                        leanh::lean_inc(v_k_x27_697_);
                        v___x_703_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_703_, 0, v_k_x27_697_);
                        leanh::lean_ctor_set(v___x_703_, 1, v___x_702_);
                        v___x_704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_704_, 0, v___x_703_);
                        return v___x_704_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v___x_705_: *mut leanh::LeanObject,
    mut v_keys_706_: *mut leanh::LeanObject,
    mut v_vals_707_: *mut leanh::LeanObject,
    mut v_i_708_: *mut leanh::LeanObject,
    mut v_k_709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_710_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_705_, v_keys_706_, v_vals_707_, v_i_708_, v_k_709_);
    leanh::lean_dec_ref(v_vals_707_);
    leanh::lean_dec_ref(v_keys_706_);
    leanh::lean_dec_ref(v___x_705_);
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
    v___x_715_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_716_ = lean_usize_sub(v___x_715_, v___x_714_);
    return v___x_716_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(
    mut v___x_717_: *mut leanh::LeanObject,
    mut v_x_718_: *mut leanh::LeanObject,
    mut v_x_719_: usize,
    mut v_x_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: usize = 0;
    let mut v___x_724_: usize = 0;
    let mut v___x_725_: usize = 0;
    let mut v_j_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u8 = 0;
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: usize = 0;
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_718_) == 0 {
                    v_es_721_ = leanh::lean_ctor_get(v_x_718_, 0);
                    leanh::lean_inc_ref(v_es_721_);
                    leanh::lean_dec_ref_known(v_x_718_, 1);
                    v___x_722_ = leanh::lean_box(2);
                    v___x_723_ = 5usize;
                    v___x_724_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_725_ = lean_usize_land(v_x_719_, v___x_724_);
                    v_j_726_ = lean_usize_to_nat(v___x_725_);
                    v___x_727_ = lean_array_get(v___x_722_, v_es_721_, v_j_726_);
                    leanh::lean_dec(v_j_726_);
                    leanh::lean_dec_ref(v_es_721_);
                    match leanh::lean_obj_tag(v___x_727_) {
                        0 => {
                            v_key_728_ = leanh::lean_ctor_get(v___x_727_, 0);
                            leanh::lean_inc_n(v_key_728_, 2);
                            v_val_729_ = leanh::lean_ctor_get(v___x_727_, 1);
                            leanh::lean_inc(v_val_729_);
                            leanh::lean_dec_ref_known(v___x_727_, 2);
                            v___x_730_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_isCongruent(v___x_717_, v_x_720_, v_key_728_);
                            if v___x_730_ == 0 {
                                leanh::lean_dec(v_val_729_);
                                leanh::lean_dec(v_key_728_);
                                v___x_731_ = leanh::lean_box(0);
                                return v___x_731_;
                            } else {
                                v___x_732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_732_, 0, v_key_728_);
                                leanh::lean_ctor_set(v___x_732_, 1, v_val_729_);
                                v___x_733_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_733_, 0, v___x_732_);
                                return v___x_733_;
                            }
                        }
                        1 => {
                            v_node_734_ = leanh::lean_ctor_get(v___x_727_, 0);
                            leanh::lean_inc(v_node_734_);
                            leanh::lean_dec_ref_known(v___x_727_, 1);
                            v___x_735_ = lean_usize_shift_right(v_x_719_, v___x_723_);
                            v_x_718_ = v_node_734_;
                            v_x_719_ = v___x_735_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_x_720_);
                            v___x_737_ = leanh::lean_box(0);
                            return v___x_737_;
                        }
                    }
                } else {
                    v_ks_738_ = leanh::lean_ctor_get(v_x_718_, 0);
                    leanh::lean_inc_ref(v_ks_738_);
                    v_vs_739_ = leanh::lean_ctor_get(v_x_718_, 1);
                    leanh::lean_inc_ref(v_vs_739_);
                    leanh::lean_dec_ref_known(v_x_718_, 2);
                    v___x_740_ = leanh::lean_unsigned_to_nat(0);
                    v___x_741_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_717_, v_ks_738_, v_vs_739_, v___x_740_, v_x_720_);
                    leanh::lean_dec_ref(v_vs_739_);
                    leanh::lean_dec_ref(v_ks_738_);
                    return v___x_741_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg___boxed(
    mut v___x_742_: *mut leanh::LeanObject,
    mut v_x_743_: *mut leanh::LeanObject,
    mut v_x_744_: *mut leanh::LeanObject,
    mut v_x_745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4773__boxed_746_: usize = 0;
    let mut v_res_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4773__boxed_746_ = leanh::lean_unbox_usize(v_x_744_);
    leanh::lean_dec(v_x_744_);
    v_res_747_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_742_, v_x_743_, v_x_4773__boxed_746_, v_x_745_);
    leanh::lean_dec_ref(v___x_742_);
    return v_res_747_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(
    mut v___x_748_: *mut leanh::LeanObject,
    mut v_x_749_: *mut leanh::LeanObject,
    mut v_x_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_751_: u64 = 0;
    let mut v___x_752_: usize = 0;
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_x_750_);
    v___x_751_ =
        l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_congrHash(v___x_748_, v_x_750_);
    v___x_752_ = lean_uint64_to_usize(v___x_751_);
    leanh::lean_inc_ref(v_x_749_);
    v___x_753_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_748_, v_x_749_, v___x_752_, v_x_750_);
    return v___x_753_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg___boxed(
    mut v___x_754_: *mut leanh::LeanObject,
    mut v_x_755_: *mut leanh::LeanObject,
    mut v_x_756_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_754_, v_x_755_, v_x_756_);
    leanh::lean_dec_ref(v_x_755_);
    leanh::lean_dec_ref(v___x_754_);
    return v_res_757_;
}
pub unsafe fn l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
    mut v_a_758_: *mut leanh::LeanObject,
    mut v_b_759_: *mut leanh::LeanObject,
    mut v_a_760_: *mut leanh::LeanObject,
    mut v_a_761_: *mut leanh::LeanObject,
    mut v_a_762_: *mut leanh::LeanObject,
    mut v_a_763_: *mut leanh::LeanObject,
    mut v_a_764_: *mut leanh::LeanObject,
    mut v_a_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_779_: u8 = 0;
    let mut v_fst_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_785_: u8 = 0;
    let mut v___x_786_: u8 = 0;
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut v_a_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut v_isSharedCheck_806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_767_ = lean_st_ref_get(v_a_760_);
                v_toGoalState_768_ = leanh::lean_ctor_get(v___x_767_, 0);
                leanh::lean_inc_ref(v_toGoalState_768_);
                leanh::lean_dec(v___x_767_);
                v_enodeMap_769_ = leanh::lean_ctor_get(v_toGoalState_768_, 1);
                leanh::lean_inc_ref(v_enodeMap_769_);
                v_congrTable_770_ = leanh::lean_ctor_get(v_toGoalState_768_, 4);
                leanh::lean_inc_ref(v_congrTable_770_);
                leanh::lean_dec_ref(v_toGoalState_768_);
                v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq;
                v_key_772_ = l_Lean_mkAppB(v___x_771_, v_a_758_, v_b_759_);
                v___x_773_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v_enodeMap_769_, v_congrTable_770_, v_key_772_);
                leanh::lean_dec_ref(v_congrTable_770_);
                leanh::lean_dec_ref(v_enodeMap_769_);
                if leanh::lean_obj_tag(v___x_773_) == 0 {
                    v___x_774_ = leanh::lean_box(0);
                    v___x_775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
                    return v___x_775_;
                } else {
                    v_val_776_ = leanh::lean_ctor_get(v___x_773_, 0);
                    v_isSharedCheck_806_ = (!leanh::lean_is_exclusive(v___x_773_)) as u8;
                    if v_isSharedCheck_806_ == 0 {
                        v___x_778_ = v___x_773_;
                        v_isShared_779_ = v_isSharedCheck_806_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_776_);
                        leanh::lean_dec(v___x_773_);
                        v___x_778_ = leanh::lean_box(0);
                        v_isShared_779_ = v_isSharedCheck_806_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_780_ = leanh::lean_ctor_get(v_val_776_, 0);
                leanh::lean_inc_n(v_fst_780_, 2);
                leanh::lean_dec(v_val_776_);
                v___x_781_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                    v_fst_780_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_,
                );
                if leanh::lean_obj_tag(v___x_781_) == 0 {
                    v_a_782_ = leanh::lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_797_ = (!leanh::lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_797_ == 0 {
                        v___x_784_ = v___x_781_;
                        v_isShared_785_ = v_isSharedCheck_797_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_782_);
                        leanh::lean_dec(v___x_781_);
                        v___x_784_ = leanh::lean_box(0);
                        v_isShared_785_ = v_isSharedCheck_797_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_780_);
                    leanh::lean_del_object(v___x_778_);
                    v_a_798_ = leanh::lean_ctor_get(v___x_781_, 0);
                    v_isSharedCheck_805_ = (!leanh::lean_is_exclusive(v___x_781_)) as u8;
                    if v_isSharedCheck_805_ == 0 {
                        v___x_800_ = v___x_781_;
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_798_);
                        leanh::lean_dec(v___x_781_);
                        v___x_800_ = leanh::lean_box(0);
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_786_ = (leanh::lean_unbox(v_a_782_) as u8);
                leanh::lean_dec(v_a_782_);
                if v___x_786_ == 0 {
                    leanh::lean_dec(v_fst_780_);
                    leanh::lean_del_object(v___x_778_);
                    v___x_787_ = leanh::lean_box(0);
                    if v_isShared_785_ == 0 {
                        leanh::lean_ctor_set(v___x_784_, 0, v___x_787_);
                        v___x_789_ = v___x_784_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_790_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
                        v___x_789_ = v_reuseFailAlloc_790_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_779_ == 0 {
                        leanh::lean_ctor_set(v___x_778_, 0, v_fst_780_);
                        v___x_792_ = v___x_778_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_796_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_796_, 0, v_fst_780_);
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
                    leanh::lean_ctor_set(v___x_784_, 0, v___x_792_);
                    v___x_794_ = v___x_784_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_795_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
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
                    v_reuseFailAlloc_804_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
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
    mut v_a_807_: *mut leanh::LeanObject,
    mut v_b_808_: *mut leanh::LeanObject,
    mut v_a_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_a_814_: *mut leanh::LeanObject,
    mut v_a_815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_816_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
        v_a_807_, v_b_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_,
    );
    leanh::lean_dec(v_a_814_);
    leanh::lean_dec_ref(v_a_813_);
    leanh::lean_dec(v_a_812_);
    leanh::lean_dec_ref(v_a_811_);
    leanh::lean_dec_ref(v_a_810_);
    leanh::lean_dec(v_a_809_);
    return v_res_816_;
}
pub unsafe fn l_Lean_Meta_Grind_getDiseqFor_x3f(
    mut v_a_817_: *mut leanh::LeanObject,
    mut v_b_818_: *mut leanh::LeanObject,
    mut v_a_819_: *mut leanh::LeanObject,
    mut v_a_820_: *mut leanh::LeanObject,
    mut v_a_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
    mut v_a_823_: *mut leanh::LeanObject,
    mut v_a_824_: *mut leanh::LeanObject,
    mut v_a_825_: *mut leanh::LeanObject,
    mut v_a_826_: *mut leanh::LeanObject,
    mut v_a_827_: *mut leanh::LeanObject,
    mut v_a_828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_830_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
        v_a_817_, v_b_818_, v_a_819_, v_a_823_, v_a_825_, v_a_826_, v_a_827_, v_a_828_,
    );
    return v___x_830_;
}
pub unsafe fn l_Lean_Meta_Grind_getDiseqFor_x3f___boxed(
    mut v_a_831_: *mut leanh::LeanObject,
    mut v_b_832_: *mut leanh::LeanObject,
    mut v_a_833_: *mut leanh::LeanObject,
    mut v_a_834_: *mut leanh::LeanObject,
    mut v_a_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
    mut v_a_837_: *mut leanh::LeanObject,
    mut v_a_838_: *mut leanh::LeanObject,
    mut v_a_839_: *mut leanh::LeanObject,
    mut v_a_840_: *mut leanh::LeanObject,
    mut v_a_841_: *mut leanh::LeanObject,
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_a_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l_Lean_Meta_Grind_getDiseqFor_x3f(
        v_a_831_, v_b_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_,
        v_a_840_, v_a_841_, v_a_842_,
    );
    leanh::lean_dec(v_a_842_);
    leanh::lean_dec_ref(v_a_841_);
    leanh::lean_dec(v_a_840_);
    leanh::lean_dec_ref(v_a_839_);
    leanh::lean_dec(v_a_838_);
    leanh::lean_dec_ref(v_a_837_);
    leanh::lean_dec(v_a_836_);
    leanh::lean_dec_ref(v_a_835_);
    leanh::lean_dec(v_a_834_);
    leanh::lean_dec(v_a_833_);
    return v_res_844_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(
    mut v___x_845_: *mut leanh::LeanObject,
    mut v_00_u03b2_846_: *mut leanh::LeanObject,
    mut v_x_847_: *mut leanh::LeanObject,
    mut v_x_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___redArg(v___x_845_, v_x_847_, v_x_848_);
    return v___x_849_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0___boxed(
    mut v___x_850_: *mut leanh::LeanObject,
    mut v_00_u03b2_851_: *mut leanh::LeanObject,
    mut v_x_852_: *mut leanh::LeanObject,
    mut v_x_853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_854_ =
        l_Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0(
            v___x_850_,
            v_00_u03b2_851_,
            v_x_852_,
            v_x_853_,
        );
    leanh::lean_dec_ref(v_x_852_);
    leanh::lean_dec_ref(v___x_850_);
    return v_res_854_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(
    mut v___x_855_: *mut leanh::LeanObject,
    mut v_00_u03b2_856_: *mut leanh::LeanObject,
    mut v_x_857_: *mut leanh::LeanObject,
    mut v_x_858_: usize,
    mut v_x_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_x_857_);
    v___x_860_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___redArg(v___x_855_, v_x_857_, v_x_858_, v_x_859_);
    return v___x_860_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0___boxed(
    mut v___x_861_: *mut leanh::LeanObject,
    mut v_00_u03b2_862_: *mut leanh::LeanObject,
    mut v_x_863_: *mut leanh::LeanObject,
    mut v_x_864_: *mut leanh::LeanObject,
    mut v_x_865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4938__boxed_866_: usize = 0;
    let mut v_res_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4938__boxed_866_ = leanh::lean_unbox_usize(v_x_864_);
    leanh::lean_dec(v_x_864_);
    v_res_867_ = l_Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0(v___x_861_, v_00_u03b2_862_, v_x_863_, v_x_4938__boxed_866_, v_x_865_);
    leanh::lean_dec_ref(v_x_863_);
    leanh::lean_dec_ref(v___x_861_);
    return v_res_867_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(
    mut v___x_868_: *mut leanh::LeanObject,
    mut v_00_u03b2_869_: *mut leanh::LeanObject,
    mut v_keys_870_: *mut leanh::LeanObject,
    mut v_vals_871_: *mut leanh::LeanObject,
    mut v_heq_872_: *mut leanh::LeanObject,
    mut v_i_873_: *mut leanh::LeanObject,
    mut v_k_874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___redArg(v___x_868_, v_keys_870_, v_vals_871_, v_i_873_, v_k_874_);
    return v___x_875_;
}
pub unsafe fn l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1___boxed(
    mut v___x_876_: *mut leanh::LeanObject,
    mut v_00_u03b2_877_: *mut leanh::LeanObject,
    mut v_keys_878_: *mut leanh::LeanObject,
    mut v_vals_879_: *mut leanh::LeanObject,
    mut v_heq_880_: *mut leanh::LeanObject,
    mut v_i_881_: *mut leanh::LeanObject,
    mut v_k_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Lean_PersistentHashMap_findEntryAtAux___at___00Lean_PersistentHashMap_findEntryAux___at___00Lean_PersistentHashMap_findEntry_x3f___at___00Lean_Meta_Grind_getDiseqFor_x3f_spec__0_spec__0_spec__1(v___x_876_, v_00_u03b2_877_, v_keys_878_, v_vals_879_, v_heq_880_, v_i_881_, v_k_882_);
    leanh::lean_dec_ref(v_vals_879_);
    leanh::lean_dec_ref(v_keys_878_);
    leanh::lean_dec_ref(v___x_876_);
    return v_res_883_;
}
pub unsafe fn l_Lean_Meta_Grind_isDiseq___redArg(
    mut v_a_884_: *mut leanh::LeanObject,
    mut v_b_885_: *mut leanh::LeanObject,
    mut v_a_886_: *mut leanh::LeanObject,
    mut v_a_887_: *mut leanh::LeanObject,
    mut v_a_888_: *mut leanh::LeanObject,
    mut v_a_889_: *mut leanh::LeanObject,
    mut v_a_890_: *mut leanh::LeanObject,
    mut v_a_891_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_a_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_893_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
                    v_a_884_, v_b_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_,
                );
                if leanh::lean_obj_tag(v___x_893_) == 0 {
                    v_a_894_ = leanh::lean_ctor_get(v___x_893_, 0);
                    v_isSharedCheck_908_ = (!leanh::lean_is_exclusive(v___x_893_)) as u8;
                    if v_isSharedCheck_908_ == 0 {
                        v___x_896_ = v___x_893_;
                        v_isShared_897_ = v_isSharedCheck_908_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_894_);
                        leanh::lean_dec(v___x_893_);
                        v___x_896_ = leanh::lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_908_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_909_ = leanh::lean_ctor_get(v___x_893_, 0);
                    v_isSharedCheck_916_ = (!leanh::lean_is_exclusive(v___x_893_)) as u8;
                    if v_isSharedCheck_916_ == 0 {
                        v___x_911_ = v___x_893_;
                        v_isShared_912_ = v_isSharedCheck_916_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_909_);
                        leanh::lean_dec(v___x_893_);
                        v___x_911_ = leanh::lean_box(0);
                        v_isShared_912_ = v_isSharedCheck_916_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_894_) == 0 {
                    v___x_898_ = 0;
                    v___x_899_ = leanh::lean_box((v___x_898_) as usize);
                    if v_isShared_897_ == 0 {
                        leanh::lean_ctor_set(v___x_896_, 0, v___x_899_);
                        v___x_901_ = v___x_896_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_902_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
                        v___x_901_ = v_reuseFailAlloc_902_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_894_, 1);
                    v___x_903_ = 1;
                    v___x_904_ = leanh::lean_box((v___x_903_) as usize);
                    if v_isShared_897_ == 0 {
                        leanh::lean_ctor_set(v___x_896_, 0, v___x_904_);
                        v___x_906_ = v___x_896_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
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
                    v_reuseFailAlloc_915_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
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
    mut v_a_917_: *mut leanh::LeanObject,
    mut v_b_918_: *mut leanh::LeanObject,
    mut v_a_919_: *mut leanh::LeanObject,
    mut v_a_920_: *mut leanh::LeanObject,
    mut v_a_921_: *mut leanh::LeanObject,
    mut v_a_922_: *mut leanh::LeanObject,
    mut v_a_923_: *mut leanh::LeanObject,
    mut v_a_924_: *mut leanh::LeanObject,
    mut v_a_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_926_ = l_Lean_Meta_Grind_isDiseq___redArg(
        v_a_917_, v_b_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_,
    );
    leanh::lean_dec(v_a_924_);
    leanh::lean_dec_ref(v_a_923_);
    leanh::lean_dec(v_a_922_);
    leanh::lean_dec_ref(v_a_921_);
    leanh::lean_dec_ref(v_a_920_);
    leanh::lean_dec(v_a_919_);
    return v_res_926_;
}
pub unsafe fn l_Lean_Meta_Grind_isDiseq(
    mut v_a_927_: *mut leanh::LeanObject,
    mut v_b_928_: *mut leanh::LeanObject,
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
    mut v_a_933_: *mut leanh::LeanObject,
    mut v_a_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
    mut v_a_936_: *mut leanh::LeanObject,
    mut v_a_937_: *mut leanh::LeanObject,
    mut v_a_938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = l_Lean_Meta_Grind_isDiseq___redArg(
        v_a_927_, v_b_928_, v_a_929_, v_a_933_, v_a_935_, v_a_936_, v_a_937_, v_a_938_,
    );
    return v___x_940_;
}
pub unsafe fn l_Lean_Meta_Grind_isDiseq___boxed(
    mut v_a_941_: *mut leanh::LeanObject,
    mut v_b_942_: *mut leanh::LeanObject,
    mut v_a_943_: *mut leanh::LeanObject,
    mut v_a_944_: *mut leanh::LeanObject,
    mut v_a_945_: *mut leanh::LeanObject,
    mut v_a_946_: *mut leanh::LeanObject,
    mut v_a_947_: *mut leanh::LeanObject,
    mut v_a_948_: *mut leanh::LeanObject,
    mut v_a_949_: *mut leanh::LeanObject,
    mut v_a_950_: *mut leanh::LeanObject,
    mut v_a_951_: *mut leanh::LeanObject,
    mut v_a_952_: *mut leanh::LeanObject,
    mut v_a_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_954_ = l_Lean_Meta_Grind_isDiseq(
        v_a_941_, v_b_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_,
        v_a_950_, v_a_951_, v_a_952_,
    );
    leanh::lean_dec(v_a_952_);
    leanh::lean_dec_ref(v_a_951_);
    leanh::lean_dec(v_a_950_);
    leanh::lean_dec_ref(v_a_949_);
    leanh::lean_dec(v_a_948_);
    leanh::lean_dec_ref(v_a_947_);
    leanh::lean_dec(v_a_946_);
    leanh::lean_dec_ref(v_a_945_);
    leanh::lean_dec(v_a_944_);
    leanh::lean_dec(v_a_943_);
    return v_res_954_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_955_ = l_Lean_Meta_Grind_instInhabitedGoalM(leanh::lean_box(0));
    return v___x_955_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(
    mut v_msg_956_: *mut leanh::LeanObject,
    mut v___y_957_: *mut leanh::LeanObject,
    mut v___y_958_: *mut leanh::LeanObject,
    mut v___y_959_: *mut leanh::LeanObject,
    mut v___y_960_: *mut leanh::LeanObject,
    mut v___y_961_: *mut leanh::LeanObject,
    mut v___y_962_: *mut leanh::LeanObject,
    mut v___y_963_: *mut leanh::LeanObject,
    mut v___y_964_: *mut leanh::LeanObject,
    mut v___y_965_: *mut leanh::LeanObject,
    mut v___y_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12288__overap_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_968_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___closed__0,
    );
    v___x_12288__overap_969_ = lean_panic_fn_borrowed(v___x_968_, v_msg_956_);
    leanh::lean_inc(v___y_966_);
    leanh::lean_inc_ref(v___y_965_);
    leanh::lean_inc(v___y_964_);
    leanh::lean_inc_ref(v___y_963_);
    leanh::lean_inc(v___y_962_);
    leanh::lean_inc_ref(v___y_961_);
    leanh::lean_inc(v___y_960_);
    leanh::lean_inc_ref(v___y_959_);
    leanh::lean_inc(v___y_958_);
    leanh::lean_inc(v___y_957_);
    v___x_970_ = leanh::lean_apply_11(
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
        leanh::lean_box(0),
    );
    return v___x_970_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0___boxed(
    mut v_msg_971_: *mut leanh::LeanObject,
    mut v___y_972_: *mut leanh::LeanObject,
    mut v___y_973_: *mut leanh::LeanObject,
    mut v___y_974_: *mut leanh::LeanObject,
    mut v___y_975_: *mut leanh::LeanObject,
    mut v___y_976_: *mut leanh::LeanObject,
    mut v___y_977_: *mut leanh::LeanObject,
    mut v___y_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
    mut v___y_980_: *mut leanh::LeanObject,
    mut v___y_981_: *mut leanh::LeanObject,
    mut v___y_982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_983_ = l_panic___at___00Lean_Meta_Grind_mkDiseqProofUsing_spec__0(
        v_msg_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_,
        v___y_978_, v___y_979_, v___y_980_, v___y_981_,
    );
    leanh::lean_dec(v___y_981_);
    leanh::lean_dec_ref(v___y_980_);
    leanh::lean_dec(v___y_979_);
    leanh::lean_dec_ref(v___y_978_);
    leanh::lean_dec(v___y_977_);
    leanh::lean_dec_ref(v___y_976_);
    leanh::lean_dec(v___y_975_);
    leanh::lean_dec_ref(v___y_974_);
    leanh::lean_dec(v___y_973_);
    leanh::lean_dec(v___y_972_);
    return v_res_983_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkDiseqProofUsing___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__2;
    v___x_988_ = leanh::lean_unsigned_to_nat(30);
    v___x_989_ = leanh::lean_unsigned_to_nat(44);
    v___x_990_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__1;
    v___x_991_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__0;
    v___x_992_ =
        l_mkPanicMessageWithDecl(v___x_991_, v___x_990_, v___x_989_, v___x_988_, v___x_987_);
    return v___x_992_;
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProofUsing(
    mut v_a_1010_: *mut leanh::LeanObject,
    mut v_b_1011_: *mut leanh::LeanObject,
    mut v_eq_1012_: *mut leanh::LeanObject,
    mut v_a_1013_: *mut leanh::LeanObject,
    mut v_a_1014_: *mut leanh::LeanObject,
    mut v_a_1015_: *mut leanh::LeanObject,
    mut v_a_1016_: *mut leanh::LeanObject,
    mut v_a_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
    mut v_a_1019_: *mut leanh::LeanObject,
    mut v_a_1020_: *mut leanh::LeanObject,
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_a_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: u8 = 0;
    let mut v_arg_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v_arg_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: u8 = 0;
    let mut v_arg_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: u8 = 0;
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v_u_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: u8 = 0;
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1115_: u8 = 0;
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: u8 = 0;
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1124_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_eq_1012_);
                v___x_1037_ = l_Lean_Expr_cleanupAnnotations(v_eq_1012_);
                v___x_1038_ = l_Lean_Expr_isApp(v___x_1037_);
                if v___x_1038_ == 0 {
                    leanh::lean_dec_ref(v___x_1037_);
                    leanh::lean_dec_ref(v_eq_1012_);
                    leanh::lean_dec_ref(v_b_1011_);
                    leanh::lean_dec_ref(v_a_1010_);
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
                    v_arg_1039_ = leanh::lean_ctor_get(v___x_1037_, 1);
                    leanh::lean_inc_ref(v_arg_1039_);
                    v___x_1040_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1037_);
                    v___x_1041_ = l_Lean_Expr_isApp(v___x_1040_);
                    if v___x_1041_ == 0 {
                        leanh::lean_dec_ref(v___x_1040_);
                        leanh::lean_dec_ref(v_arg_1039_);
                        leanh::lean_dec_ref(v_eq_1012_);
                        leanh::lean_dec_ref(v_b_1011_);
                        leanh::lean_dec_ref(v_a_1010_);
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
                        v_arg_1042_ = leanh::lean_ctor_get(v___x_1040_, 1);
                        leanh::lean_inc_ref(v_arg_1042_);
                        v___x_1043_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1040_);
                        v___x_1044_ = l_Lean_Expr_isApp(v___x_1043_);
                        if v___x_1044_ == 0 {
                            leanh::lean_dec_ref(v___x_1043_);
                            leanh::lean_dec_ref(v_arg_1042_);
                            leanh::lean_dec_ref(v_arg_1039_);
                            leanh::lean_dec_ref(v_eq_1012_);
                            leanh::lean_dec_ref(v_b_1011_);
                            leanh::lean_dec_ref(v_a_1010_);
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
                            v_arg_1045_ = leanh::lean_ctor_get(v___x_1043_, 1);
                            leanh::lean_inc_ref(v_arg_1045_);
                            v___x_1046_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1043_);
                            v___x_1047_ = l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq___closed__1;
                            v___x_1048_ = l_Lean_Expr_isConstOf(v___x_1046_, v___x_1047_);
                            if v___x_1048_ == 0 {
                                leanh::lean_dec_ref(v___x_1046_);
                                leanh::lean_dec_ref(v_arg_1045_);
                                leanh::lean_dec_ref(v_arg_1042_);
                                leanh::lean_dec_ref(v_arg_1039_);
                                leanh::lean_dec_ref(v_eq_1012_);
                                leanh::lean_dec_ref(v_b_1011_);
                                leanh::lean_dec_ref(v_a_1010_);
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
                                leanh::lean_inc_ref(v_eq_1012_);
                                v___x_1049_ = l_Lean_Meta_Grind_mkEqFalseProof(
                                    v_eq_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_,
                                    v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_,
                                    v_a_1022_,
                                );
                                if leanh::lean_obj_tag(v___x_1049_) == 0 {
                                    v_a_1050_ = leanh::lean_ctor_get(v___x_1049_, 0);
                                    v_isSharedCheck_1124_ =
                                        (!leanh::lean_is_exclusive(v___x_1049_)) as u8;
                                    if v_isSharedCheck_1124_ == 0 {
                                        v___x_1052_ = v___x_1049_;
                                        v_isShared_1053_ = v_isSharedCheck_1124_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_1050_);
                                        leanh::lean_dec(v___x_1049_);
                                        v___x_1052_ = leanh::lean_box(0);
                                        v_isShared_1053_ = v_isSharedCheck_1124_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_1046_);
                                    leanh::lean_dec_ref(v_arg_1045_);
                                    leanh::lean_dec_ref(v_arg_1042_);
                                    leanh::lean_dec_ref(v_arg_1039_);
                                    leanh::lean_dec_ref(v_eq_1012_);
                                    leanh::lean_dec_ref(v_b_1011_);
                                    leanh::lean_dec_ref(v_a_1010_);
                                    return v___x_1049_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1035_ = leanh::lean_obj_once(
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
                leanh::lean_dec_ref(v___x_1046_);
                v___x_1104_ = l_Lean_Meta_mkOfEqFalseCore(v_eq_1012_, v_a_1050_);
                v___x_1120_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1010_, v_arg_1042_, v_a_1013_);
                if leanh::lean_obj_tag(v___x_1120_) == 0 {
                    v_a_1121_ = leanh::lean_ctor_get(v___x_1120_, 0);
                    leanh::lean_inc(v_a_1121_);
                    v___x_1122_ = (leanh::lean_unbox(v_a_1121_) as u8);
                    leanh::lean_dec(v_a_1121_);
                    if v___x_1122_ == 0 {
                        v___y_1106_ = v___x_1120_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v___x_1120_, 1);
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
                    leanh::lean_del_object(v___x_1052_);
                    leanh::lean_inc(v___y_1067_);
                    leanh::lean_inc_ref(v___y_1066_);
                    leanh::lean_inc(v___y_1065_);
                    leanh::lean_inc_ref(v___y_1064_);
                    leanh::lean_inc(v___y_1063_);
                    leanh::lean_inc_ref(v___y_1062_);
                    leanh::lean_inc(v___y_1061_);
                    leanh::lean_inc_ref(v___y_1060_);
                    leanh::lean_inc(v___y_1059_);
                    leanh::lean_inc(v___y_1058_);
                    leanh::lean_inc_ref(v___y_1056_);
                    leanh::lean_inc_ref(v_b_1011_);
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
                    if leanh::lean_obj_tag(v___x_1069_) == 0 {
                        v_a_1070_ = leanh::lean_ctor_get(v___x_1069_, 0);
                        v_isSharedCheck_1080_ =
                            (!leanh::lean_is_exclusive(v___x_1069_)) as u8;
                        if v_isSharedCheck_1080_ == 0 {
                            v___x_1072_ = v___x_1069_;
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1070_);
                            leanh::lean_dec(v___x_1069_);
                            v___x_1072_ = leanh::lean_box(0);
                            v_isShared_1073_ = v_isSharedCheck_1080_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_h_1057_);
                        leanh::lean_dec_ref(v___y_1056_);
                        leanh::lean_dec(v_u_1054_);
                        leanh::lean_dec_ref(v_arg_1045_);
                        leanh::lean_dec_ref(v_b_1011_);
                        leanh::lean_dec_ref(v_a_1010_);
                        return v___x_1069_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_1056_);
                    leanh::lean_dec(v_u_1054_);
                    leanh::lean_dec_ref(v_arg_1045_);
                    leanh::lean_dec_ref(v_b_1011_);
                    leanh::lean_dec_ref(v_a_1010_);
                    if v_isShared_1053_ == 0 {
                        leanh::lean_ctor_set(v___x_1052_, 0, v_h_1057_);
                        v___x_1082_ = v___x_1052_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1083_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_h_1057_);
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
                    leanh::lean_ctor_set(v___x_1072_, 0, v___x_1076_);
                    v___x_1078_ = v___x_1072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1079_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
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
                    leanh::lean_inc(v___y_1097_);
                    leanh::lean_inc_ref(v___y_1096_);
                    leanh::lean_inc(v___y_1095_);
                    leanh::lean_inc_ref(v___y_1094_);
                    leanh::lean_inc(v___y_1093_);
                    leanh::lean_inc_ref(v___y_1092_);
                    leanh::lean_inc(v___y_1091_);
                    leanh::lean_inc_ref(v___y_1090_);
                    leanh::lean_inc(v___y_1089_);
                    leanh::lean_inc(v___y_1088_);
                    leanh::lean_inc_ref(v_fst_1085_);
                    leanh::lean_inc_ref(v_a_1010_);
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
                    if leanh::lean_obj_tag(v___x_1099_) == 0 {
                        v_a_1100_ = leanh::lean_ctor_get(v___x_1099_, 0);
                        leanh::lean_inc(v_a_1100_);
                        leanh::lean_dec_ref_known(v___x_1099_, 1);
                        v___x_1101_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__9;
                        leanh::lean_inc(v_u_1054_);
                        v___x_1102_ = l_Lean_mkConst(v___x_1101_, v_u_1054_);
                        leanh::lean_inc_ref(v_fst_1086_);
                        leanh::lean_inc_ref(v_a_1010_);
                        leanh::lean_inc_ref(v_arg_1045_);
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
                        leanh::lean_dec_ref(v_snd_1087_);
                        leanh::lean_dec_ref(v_fst_1086_);
                        leanh::lean_dec_ref(v_fst_1085_);
                        leanh::lean_dec(v_u_1054_);
                        leanh::lean_del_object(v___x_1052_);
                        leanh::lean_dec_ref(v_arg_1045_);
                        leanh::lean_dec_ref(v_b_1011_);
                        leanh::lean_dec_ref(v_a_1010_);
                        return v___x_1099_;
                    }
                } else {
                    leanh::lean_dec_ref(v_fst_1085_);
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
                if leanh::lean_obj_tag(v___y_1106_) == 0 {
                    v_a_1107_ = leanh::lean_ctor_get(v___y_1106_, 0);
                    leanh::lean_inc(v_a_1107_);
                    leanh::lean_dec_ref_known(v___y_1106_, 1);
                    v___x_1108_ = (leanh::lean_unbox(v_a_1107_) as u8);
                    leanh::lean_dec(v_a_1107_);
                    if v___x_1108_ == 0 {
                        v___x_1109_ = l_Lean_Meta_Grind_mkDiseqProofUsing___closed__12;
                        leanh::lean_inc(v_u_1054_);
                        v___x_1110_ = l_Lean_mkConst(v___x_1109_, v_u_1054_);
                        leanh::lean_inc_ref(v_arg_1039_);
                        leanh::lean_inc_ref(v_arg_1042_);
                        leanh::lean_inc_ref(v_arg_1045_);
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
                    leanh::lean_dec_ref(v___x_1104_);
                    leanh::lean_dec(v_u_1054_);
                    leanh::lean_del_object(v___x_1052_);
                    leanh::lean_dec_ref(v_arg_1045_);
                    leanh::lean_dec_ref(v_arg_1042_);
                    leanh::lean_dec_ref(v_arg_1039_);
                    leanh::lean_dec_ref(v_b_1011_);
                    leanh::lean_dec_ref(v_a_1010_);
                    v_a_1112_ = leanh::lean_ctor_get(v___y_1106_, 0);
                    v_isSharedCheck_1119_ = (!leanh::lean_is_exclusive(v___y_1106_)) as u8;
                    if v_isSharedCheck_1119_ == 0 {
                        v___x_1114_ = v___y_1106_;
                        v_isShared_1115_ = v_isSharedCheck_1119_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1112_);
                        leanh::lean_dec(v___y_1106_);
                        v___x_1114_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1118_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
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
    mut v_a_1125_: *mut leanh::LeanObject,
    mut v_b_1126_: *mut leanh::LeanObject,
    mut v_eq_1127_: *mut leanh::LeanObject,
    mut v_a_1128_: *mut leanh::LeanObject,
    mut v_a_1129_: *mut leanh::LeanObject,
    mut v_a_1130_: *mut leanh::LeanObject,
    mut v_a_1131_: *mut leanh::LeanObject,
    mut v_a_1132_: *mut leanh::LeanObject,
    mut v_a_1133_: *mut leanh::LeanObject,
    mut v_a_1134_: *mut leanh::LeanObject,
    mut v_a_1135_: *mut leanh::LeanObject,
    mut v_a_1136_: *mut leanh::LeanObject,
    mut v_a_1137_: *mut leanh::LeanObject,
    mut v_a_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1139_ = l_Lean_Meta_Grind_mkDiseqProofUsing(
        v_a_1125_, v_b_1126_, v_eq_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_,
        v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_,
    );
    leanh::lean_dec(v_a_1137_);
    leanh::lean_dec_ref(v_a_1136_);
    leanh::lean_dec(v_a_1135_);
    leanh::lean_dec_ref(v_a_1134_);
    leanh::lean_dec(v_a_1133_);
    leanh::lean_dec_ref(v_a_1132_);
    leanh::lean_dec(v_a_1131_);
    leanh::lean_dec_ref(v_a_1130_);
    leanh::lean_dec(v_a_1129_);
    leanh::lean_dec(v_a_1128_);
    return v_res_1139_;
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProof_x3f(
    mut v_a_1140_: *mut leanh::LeanObject,
    mut v_b_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
    mut v_a_1143_: *mut leanh::LeanObject,
    mut v_a_1144_: *mut leanh::LeanObject,
    mut v_a_1145_: *mut leanh::LeanObject,
    mut v_a_1146_: *mut leanh::LeanObject,
    mut v_a_1147_: *mut leanh::LeanObject,
    mut v_a_1148_: *mut leanh::LeanObject,
    mut v_a_1149_: *mut leanh::LeanObject,
    mut v_a_1150_: *mut leanh::LeanObject,
    mut v_a_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1157_: u8 = 0;
    let mut v_val_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1166_: u8 = 0;
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v_a_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_isSharedCheck_1182_: u8 = 0;
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1187_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_b_1141_);
                leanh::lean_inc_ref(v_a_1140_);
                v___x_1153_ = l_Lean_Meta_Grind_getDiseqFor_x3f___redArg(
                    v_a_1140_, v_b_1141_, v_a_1142_, v_a_1146_, v_a_1148_, v_a_1149_, v_a_1150_,
                    v_a_1151_,
                );
                if leanh::lean_obj_tag(v___x_1153_) == 0 {
                    v_a_1154_ = leanh::lean_ctor_get(v___x_1153_, 0);
                    v_isSharedCheck_1187_ = (!leanh::lean_is_exclusive(v___x_1153_)) as u8;
                    if v_isSharedCheck_1187_ == 0 {
                        v___x_1156_ = v___x_1153_;
                        v_isShared_1157_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1154_);
                        leanh::lean_dec(v___x_1153_);
                        v___x_1156_ = leanh::lean_box(0);
                        v_isShared_1157_ = v_isSharedCheck_1187_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_1141_);
                    leanh::lean_dec_ref(v_a_1140_);
                    return v___x_1153_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1154_) == 1 {
                    leanh::lean_del_object(v___x_1156_);
                    v_val_1158_ = leanh::lean_ctor_get(v_a_1154_, 0);
                    v_isSharedCheck_1182_ = (!leanh::lean_is_exclusive(v_a_1154_)) as u8;
                    if v_isSharedCheck_1182_ == 0 {
                        v___x_1160_ = v_a_1154_;
                        v_isShared_1161_ = v_isSharedCheck_1182_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1158_);
                        leanh::lean_dec(v_a_1154_);
                        v___x_1160_ = leanh::lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1182_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1154_);
                    leanh::lean_dec_ref(v_b_1141_);
                    leanh::lean_dec_ref(v_a_1140_);
                    v___x_1183_ = leanh::lean_box(0);
                    if v_isShared_1157_ == 0 {
                        leanh::lean_ctor_set(v___x_1156_, 0, v___x_1183_);
                        v___x_1185_ = v___x_1156_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
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
                if leanh::lean_obj_tag(v___x_1162_) == 0 {
                    v_a_1163_ = leanh::lean_ctor_get(v___x_1162_, 0);
                    v_isSharedCheck_1173_ = (!leanh::lean_is_exclusive(v___x_1162_)) as u8;
                    if v_isSharedCheck_1173_ == 0 {
                        v___x_1165_ = v___x_1162_;
                        v_isShared_1166_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1163_);
                        leanh::lean_dec(v___x_1162_);
                        v___x_1165_ = leanh::lean_box(0);
                        v_isShared_1166_ = v_isSharedCheck_1173_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1160_);
                    v_a_1174_ = leanh::lean_ctor_get(v___x_1162_, 0);
                    v_isSharedCheck_1181_ = (!leanh::lean_is_exclusive(v___x_1162_)) as u8;
                    if v_isSharedCheck_1181_ == 0 {
                        v___x_1176_ = v___x_1162_;
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1174_);
                        leanh::lean_dec(v___x_1162_);
                        v___x_1176_ = leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1161_ == 0 {
                    leanh::lean_ctor_set(v___x_1160_, 0, v_a_1163_);
                    v___x_1168_ = v___x_1160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1163_);
                    v___x_1168_ = v_reuseFailAlloc_1172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1166_ == 0 {
                    leanh::lean_ctor_set(v___x_1165_, 0, v___x_1168_);
                    v___x_1170_ = v___x_1165_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
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
                    v_reuseFailAlloc_1180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
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
    mut v_a_1188_: *mut leanh::LeanObject,
    mut v_b_1189_: *mut leanh::LeanObject,
    mut v_a_1190_: *mut leanh::LeanObject,
    mut v_a_1191_: *mut leanh::LeanObject,
    mut v_a_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
    mut v_a_1194_: *mut leanh::LeanObject,
    mut v_a_1195_: *mut leanh::LeanObject,
    mut v_a_1196_: *mut leanh::LeanObject,
    mut v_a_1197_: *mut leanh::LeanObject,
    mut v_a_1198_: *mut leanh::LeanObject,
    mut v_a_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1201_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(
        v_a_1188_, v_b_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_,
        v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_,
    );
    leanh::lean_dec(v_a_1199_);
    leanh::lean_dec_ref(v_a_1198_);
    leanh::lean_dec(v_a_1197_);
    leanh::lean_dec_ref(v_a_1196_);
    leanh::lean_dec(v_a_1195_);
    leanh::lean_dec_ref(v_a_1194_);
    leanh::lean_dec(v_a_1193_);
    leanh::lean_dec_ref(v_a_1192_);
    leanh::lean_dec(v_a_1191_);
    leanh::lean_dec(v_a_1190_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(
    mut v_msgData_1202_: *mut leanh::LeanObject,
    mut v___y_1203_: *mut leanh::LeanObject,
    mut v___y_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = lean_st_ref_get(v___y_1206_);
    v_env_1209_ = leanh::lean_ctor_get(v___x_1208_, 0);
    leanh::lean_inc_ref(v_env_1209_);
    leanh::lean_dec(v___x_1208_);
    v___x_1210_ = lean_st_ref_get(v___y_1204_);
    v_mctx_1211_ = leanh::lean_ctor_get(v___x_1210_, 0);
    leanh::lean_inc_ref(v_mctx_1211_);
    leanh::lean_dec(v___x_1210_);
    v_lctx_1212_ = leanh::lean_ctor_get(v___y_1203_, 2);
    v_options_1213_ = leanh::lean_ctor_get(v___y_1205_, 2);
    leanh::lean_inc_ref(v_options_1213_);
    leanh::lean_inc_ref(v_lctx_1212_);
    v___x_1214_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1214_, 0, v_env_1209_);
    leanh::lean_ctor_set(v___x_1214_, 1, v_mctx_1211_);
    leanh::lean_ctor_set(v___x_1214_, 2, v_lctx_1212_);
    leanh::lean_ctor_set(v___x_1214_, 3, v_options_1213_);
    v___x_1215_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
    leanh::lean_ctor_set(v___x_1215_, 1, v_msgData_1202_);
    v___x_1216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1216_, 0, v___x_1215_);
    return v___x_1216_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0___boxed(
    mut v_msgData_1217_: *mut leanh::LeanObject,
    mut v___y_1218_: *mut leanh::LeanObject,
    mut v___y_1219_: *mut leanh::LeanObject,
    mut v___y_1220_: *mut leanh::LeanObject,
    mut v___y_1221_: *mut leanh::LeanObject,
    mut v___y_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1223_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msgData_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
    leanh::lean_dec(v___y_1221_);
    leanh::lean_dec_ref(v___y_1220_);
    leanh::lean_dec(v___y_1219_);
    leanh::lean_dec_ref(v___y_1218_);
    return v_res_1223_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(
    mut v_msg_1224_: *mut leanh::LeanObject,
    mut v___y_1225_: *mut leanh::LeanObject,
    mut v___y_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
    mut v___y_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1235_: u8 = 0;
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1230_ = leanh::lean_ctor_get(v___y_1227_, 5);
                v___x_1231_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0_spec__0(v_msg_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
                v_a_1232_ = leanh::lean_ctor_get(v___x_1231_, 0);
                v_isSharedCheck_1240_ = (!leanh::lean_is_exclusive(v___x_1231_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v___x_1234_ = v___x_1231_;
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1232_);
                    leanh::lean_dec(v___x_1231_);
                    v___x_1234_ = leanh::lean_box(0);
                    v_isShared_1235_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1230_);
                v___x_1236_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1236_, 0, v_ref_1230_);
                leanh::lean_ctor_set(v___x_1236_, 1, v_a_1232_);
                if v_isShared_1235_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1234_, 1);
                    leanh::lean_ctor_set(v___x_1234_, 0, v___x_1236_);
                    v___x_1238_ = v___x_1234_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
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
    mut v_msg_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
    mut v___y_1243_: *mut leanh::LeanObject,
    mut v___y_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1247_ = l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0___redArg(
        v_msg_1241_,
        v___y_1242_,
        v___y_1243_,
        v___y_1244_,
        v___y_1245_,
    );
    leanh::lean_dec(v___y_1245_);
    leanh::lean_dec_ref(v___y_1244_);
    leanh::lean_dec(v___y_1243_);
    leanh::lean_dec_ref(v___y_1242_);
    return v_res_1247_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l_Lean_Meta_Grind_mkDiseqProof___closed__0;
    v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lean_Meta_Grind_mkDiseqProof___closed__2;
    v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn l_Lean_Meta_Grind_mkDiseqProof(
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v_b_1255_: *mut leanh::LeanObject,
    mut v_a_1256_: *mut leanh::LeanObject,
    mut v_a_1257_: *mut leanh::LeanObject,
    mut v_a_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
    mut v_a_1261_: *mut leanh::LeanObject,
    mut v_a_1262_: *mut leanh::LeanObject,
    mut v_a_1263_: *mut leanh::LeanObject,
    mut v_a_1264_: *mut leanh::LeanObject,
    mut v_a_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v_val_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1284_: u8 = 0;
    let mut v_a_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1288_: u8 = 0;
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_b_1255_);
                leanh::lean_inc_ref(v_a_1254_);
                v___x_1267_ = l_Lean_Meta_Grind_mkDiseqProof_x3f(
                    v_a_1254_, v_b_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_,
                    v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_,
                );
                if leanh::lean_obj_tag(v___x_1267_) == 0 {
                    v_a_1268_ = leanh::lean_ctor_get(v___x_1267_, 0);
                    v_isSharedCheck_1284_ = (!leanh::lean_is_exclusive(v___x_1267_)) as u8;
                    if v_isSharedCheck_1284_ == 0 {
                        v___x_1270_ = v___x_1267_;
                        v_isShared_1271_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1268_);
                        leanh::lean_dec(v___x_1267_);
                        v___x_1270_ = leanh::lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1284_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_b_1255_);
                    leanh::lean_dec_ref(v_a_1254_);
                    v_a_1285_ = leanh::lean_ctor_get(v___x_1267_, 0);
                    v_isSharedCheck_1292_ = (!leanh::lean_is_exclusive(v___x_1267_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1287_ = v___x_1267_;
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1285_);
                        leanh::lean_dec(v___x_1267_);
                        v___x_1287_ = leanh::lean_box(0);
                        v_isShared_1288_ = v_isSharedCheck_1292_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1268_) == 1 {
                    leanh::lean_dec_ref(v_b_1255_);
                    leanh::lean_dec_ref(v_a_1254_);
                    v_val_1272_ = leanh::lean_ctor_get(v_a_1268_, 0);
                    leanh::lean_inc(v_val_1272_);
                    leanh::lean_dec_ref_known(v_a_1268_, 1);
                    if v_isShared_1271_ == 0 {
                        leanh::lean_ctor_set(v___x_1270_, 0, v_val_1272_);
                        v___x_1274_ = v___x_1270_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1275_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_val_1272_);
                        v___x_1274_ = v_reuseFailAlloc_1275_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1270_);
                    leanh::lean_dec(v_a_1268_);
                    v___x_1276_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__1_once),
                        _init_l_Lean_Meta_Grind_mkDiseqProof___closed__1,
                    );
                    v___x_1277_ = l_Lean_indentExpr(v_a_1254_);
                    v___x_1278_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1278_, 0, v___x_1276_);
                    leanh::lean_ctor_set(v___x_1278_, 1, v___x_1277_);
                    v___x_1279_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_mkDiseqProof___closed__3_once),
                        _init_l_Lean_Meta_Grind_mkDiseqProof___closed__3,
                    );
                    v___x_1280_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1280_, 0, v___x_1278_);
                    leanh::lean_ctor_set(v___x_1280_, 1, v___x_1279_);
                    v___x_1281_ = l_Lean_indentExpr(v_b_1255_);
                    v___x_1282_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1282_, 0, v___x_1280_);
                    leanh::lean_ctor_set(v___x_1282_, 1, v___x_1281_);
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
                    v_reuseFailAlloc_1291_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
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
    mut v_a_1293_: *mut leanh::LeanObject,
    mut v_b_1294_: *mut leanh::LeanObject,
    mut v_a_1295_: *mut leanh::LeanObject,
    mut v_a_1296_: *mut leanh::LeanObject,
    mut v_a_1297_: *mut leanh::LeanObject,
    mut v_a_1298_: *mut leanh::LeanObject,
    mut v_a_1299_: *mut leanh::LeanObject,
    mut v_a_1300_: *mut leanh::LeanObject,
    mut v_a_1301_: *mut leanh::LeanObject,
    mut v_a_1302_: *mut leanh::LeanObject,
    mut v_a_1303_: *mut leanh::LeanObject,
    mut v_a_1304_: *mut leanh::LeanObject,
    mut v_a_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1306_ = l_Lean_Meta_Grind_mkDiseqProof(
        v_a_1293_, v_b_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_,
        v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_,
    );
    leanh::lean_dec(v_a_1304_);
    leanh::lean_dec_ref(v_a_1303_);
    leanh::lean_dec(v_a_1302_);
    leanh::lean_dec_ref(v_a_1301_);
    leanh::lean_dec(v_a_1300_);
    leanh::lean_dec_ref(v_a_1299_);
    leanh::lean_dec(v_a_1298_);
    leanh::lean_dec_ref(v_a_1297_);
    leanh::lean_dec(v_a_1296_);
    leanh::lean_dec(v_a_1295_);
    return v_res_1306_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_mkDiseqProof_spec__0(
    mut v_00_u03b1_1307_: *mut leanh::LeanObject,
    mut v_msg_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
    mut v___y_1311_: *mut leanh::LeanObject,
    mut v___y_1312_: *mut leanh::LeanObject,
    mut v___y_1313_: *mut leanh::LeanObject,
    mut v___y_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1321_: *mut leanh::LeanObject,
    mut v_msg_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
    mut v___y_1330_: *mut leanh::LeanObject,
    mut v___y_1331_: *mut leanh::LeanObject,
    mut v___y_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1332_);
    leanh::lean_dec_ref(v___y_1331_);
    leanh::lean_dec(v___y_1330_);
    leanh::lean_dec_ref(v___y_1329_);
    leanh::lean_dec(v___y_1328_);
    leanh::lean_dec_ref(v___y_1327_);
    leanh::lean_dec(v___y_1326_);
    leanh::lean_dec_ref(v___y_1325_);
    leanh::lean_dec(v___y_1324_);
    leanh::lean_dec(v___y_1323_);
    return v_res_1334_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq =
        _init_l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq();
    leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Diseq_0__Lean_Meta_Grind_dummyEq,
    );
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Diseq(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Diseq(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
}