// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_mkStr6,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkApp9, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::{
    l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVPred::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value: LeanStringObject<
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
    m_data: [69, 113, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1_value: LeanStringObject<
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
    m_data: [114, 101, 102, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value)
            as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1_value)
            as *mut LeanObject,
        13480818501600609864 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value: LeanStringObject<
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
    m_data: [66, 111, 111, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value)
            as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 110, 115, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value)
            as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0_value)
            as *mut LeanObject,
        17532416664988428445 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value:
    LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 86, 68, 101, 99, 105, 100, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [66, 86, 76, 111, 103, 105, 99, 97, 108, 69, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4_value:
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
    m_data: [101, 118, 97, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value
        ) as *mut LeanObject,
        15170596904992606634 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4_value
        ) as *mut LeanObject,
        13807464631116737617 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [66, 111, 111, 108, 69, 120, 112, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value:
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
    m_data: [108, 105, 116, 101, 114, 97, 108, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value
        ) as *mut LeanObject,
        5051218143360974414 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value
        ) as *mut LeanObject,
        849521351811639932 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [66, 86, 80, 114, 101, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4_value
        ) as *mut LeanObject,
        18198180362361044236 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [99, 111, 110, 115, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value) as *mut LeanObject,5051218143360974414 as *mut LeanObject] };
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value) as *mut LeanObject,7733665888557906164 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value)
            as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4_value) as *mut LeanObject,15761733860085307253 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7_value:
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
    m_data: [116, 114, 117, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value)
            as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7_value) as *mut LeanObject,9255189395584251158 as *mut LeanObject] };
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 102, 108, 101, 99, 116, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value) as *mut LeanObject,7340257369084348989 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1_value) as *mut LeanObject,10562676050558293266 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [120, 111, 114, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value) as *mut LeanObject,7340257369084348989 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3_value) as *mut LeanObject,10338135696689434255 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [98, 101, 113, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value) as *mut LeanObject,7340257369084348989 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5_value) as *mut LeanObject,3034827292988699493 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 114, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value) as *mut LeanObject,5139300886809190733 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value) as *mut LeanObject,17363264175708149920 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value) as *mut LeanObject,18076273821967539232 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value) as *mut LeanObject,7340257369084348989 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7_value) as *mut LeanObject,7097633491000915127 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value:
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
    m_data: [103, 97, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value
        ) as *mut LeanObject,
        5051218143360974414 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value
        ) as *mut LeanObject,
        16066464032356577345 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value:
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
    m_data: [71, 97, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4_value:
    LeanStringObject<4> = LeanStringObject {
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
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value
        ) as *mut LeanObject,
        13347281081598155225 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4_value
        ) as *mut LeanObject,
        8714298000618519999 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [120, 111, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value
        ) as *mut LeanObject,
        13347281081598155225 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7_value
        ) as *mut LeanObject,
        4160575121790354240 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [98, 101, 113, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value
        ) as *mut LeanObject,
        13347281081598155225 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10_value
        ) as *mut LeanObject,
        14669553018067580624 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [111, 114, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value
        ) as *mut LeanObject,
        13347281081598155225 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13_value
        ) as *mut LeanObject,
        4514021465289239077 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 116, 95, 99, 111, 110, 103, 114, 0]};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 111, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value
        ) as *mut LeanObject,
        5051218143360974414 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value
        ) as *mut LeanObject,
        15553663127940073204 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value
) as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value
        ) as *mut LeanObject,
        5051218143360974414 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value
        ) as *mut LeanObject,
        5435855234965385182 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value
) as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3()
-> *mut LeanObject {
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    v___x_866_ = lean_unsigned_to_nat(1);
    v___x_867_ = l_Lean_Level_ofNat(v___x_866_);
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4()
-> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_868_ = lean_box(0);
    v___x_869_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3,
    );
    v___x_870_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_870_, 0, v___x_869_);
    lean_ctor_set(v___x_870_, 1, v___x_868_);
    return v___x_870_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5()
-> *mut LeanObject {
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    v___x_871_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4,
    );
    v___x_872_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2;
    v___x_873_ = l_Lean_mkConst(v___x_872_, v___x_871_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8()
-> *mut LeanObject {
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    v___x_877_ = lean_box(0);
    v___x_878_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7;
    v___x_879_ = l_Lean_mkConst(v___x_878_, v___x_877_);
    return v___x_879_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(
    mut v_expr_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    v___x_881_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5,
    );
    v___x_882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8,
    );
    v___x_883_ = l_Lean_mkAppB(v___x_881_, v___x_882_, v_expr_880_);
    return v___x_883_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2()
-> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    v___x_888_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4,
    );
    v___x_889_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1;
    v___x_890_ = l_Lean_mkConst(v___x_889_, v___x_888_);
    return v___x_890_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(
    mut v_x_891_: *mut LeanObject,
    mut v_y_892_: *mut LeanObject,
    mut v_z_893_: *mut LeanObject,
    mut v_hxy_894_: *mut LeanObject,
    mut v_hyz_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    v___x_896_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2,
    );
    v___x_897_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8,
    );
    v___x_898_ = l_Lean_mkApp6(
        v___x_896_, v___x_897_, v_x_891_, v_y_892_, v_z_893_, v_hxy_894_, v_hyz_895_,
    );
    return v___x_898_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6()
-> *mut LeanObject {
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    v___x_910_ = lean_box(0);
    v___x_911_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5;
    v___x_912_ = l_Lean_mkConst(v___x_911_, v___x_910_);
    return v___x_912_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
    mut v_expr_913_: *mut LeanObject,
    mut v_a_914_: *mut LeanObject,
    mut v_a_915_: *mut LeanObject,
    mut v_a_916_: *mut LeanObject,
    mut v_a_917_: *mut LeanObject,
    mut v_a_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_924_: u8 = 0;
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_920_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(
                    v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_,
                );
                if lean_obj_tag(v___x_920_) == 0 {
                    v_a_921_ = lean_ctor_get(v___x_920_, 0);
                    v_isSharedCheck_930_ = (!lean_is_exclusive(v___x_920_)) as u8;
                    if v_isSharedCheck_930_ == 0 {
                        v___x_923_ = v___x_920_;
                        v_isShared_924_ = v_isSharedCheck_930_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_921_);
                        lean_dec(v___x_920_);
                        v___x_923_ = lean_box(0);
                        v_isShared_924_ = v_isSharedCheck_930_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_expr_913_);
                    return v___x_920_;
                }
            }
            1 => {
                v___x_925_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6,
                );
                v___x_926_ = l_Lean_mkAppB(v___x_925_, v_a_921_, v_expr_913_);
                if v_isShared_924_ == 0 {
                    lean_ctor_set(v___x_923_, 0, v___x_926_);
                    v___x_928_ = v___x_923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
                    v___x_928_ = v_reuseFailAlloc_929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___boxed(
    mut v_expr_931_: *mut LeanObject,
    mut v_a_932_: *mut LeanObject,
    mut v_a_933_: *mut LeanObject,
    mut v_a_934_: *mut LeanObject,
    mut v_a_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
    mut v_a_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_938_: *mut LeanObject = core::ptr::null_mut();
    v_res_938_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
        v_expr_931_,
        v_a_932_,
        v_a_933_,
        v_a_934_,
        v_a_935_,
        v_a_936_,
    );
    lean_dec(v_a_936_);
    lean_dec_ref(v_a_935_);
    lean_dec(v_a_934_);
    lean_dec_ref(v_a_933_);
    lean_dec(v_a_932_);
    return v_res_938_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    v___x_947_ = lean_box(0);
    v___x_948_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2;
    v___x_949_ = l_Lean_mkConst(v___x_948_, v___x_947_);
    return v___x_949_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    v___x_956_ = lean_box(0);
    v___x_957_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5;
    v___x_958_ = l_Lean_mkConst(v___x_957_, v___x_956_);
    return v___x_958_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(
    mut v_bvPred_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bvPred_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_originalExpr_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_boolExpr_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v_bvPred_961_ = lean_ctor_get(v_bvPred_959_, 0);
    v_originalExpr_962_ = lean_ctor_get(v_bvPred_959_, 1);
    lean_inc_ref(v_originalExpr_962_);
    v_expr_963_ = lean_ctor_get(v_bvPred_959_, 3);
    lean_inc_ref(v_bvPred_961_);
    v_boolExpr_964_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v_boolExpr_964_, 0, v_bvPred_961_);
    v___x_965_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3,
    );
    v___x_966_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6,
    );
    lean_inc_ref(v_expr_963_);
    v_expr_967_ = l_Lean_mkAppB(v___x_965_, v___x_966_, v_expr_963_);
    v_proof_968_ = lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v_proof_968_, 0, v_bvPred_959_);
    v___x_969_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_969_, 0, v_boolExpr_964_);
    lean_ctor_set(v___x_969_, 1, v_originalExpr_962_);
    lean_ctor_set(v___x_969_, 2, v_proof_968_);
    lean_ctor_set(v___x_969_, 3, v_expr_967_);
    v___x_970_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_970_, 0, v___x_969_);
    return v___x_970_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___boxed(
    mut v_bvPred_971_: *mut LeanObject,
    mut v_a_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_973_: *mut LeanObject = core::ptr::null_mut();
    v_res_973_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_bvPred_971_);
    return v_res_973_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(
    mut v_bvPred_974_: *mut LeanObject,
    mut v_a_975_: *mut LeanObject,
    mut v_a_976_: *mut LeanObject,
    mut v_a_977_: *mut LeanObject,
    mut v_a_978_: *mut LeanObject,
    mut v_a_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_981_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_bvPred_974_);
    return v___x_981_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___boxed(
    mut v_bvPred_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
    mut v_a_984_: *mut LeanObject,
    mut v_a_985_: *mut LeanObject,
    mut v_a_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_989_: *mut LeanObject = core::ptr::null_mut();
    v_res_989_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(
        v_bvPred_982_,
        v_a_983_,
        v_a_984_,
        v_a_985_,
        v_a_986_,
        v_a_987_,
    );
    lean_dec(v_a_987_);
    lean_dec_ref(v_a_986_);
    lean_dec(v_a_985_);
    lean_dec_ref(v_a_984_);
    lean_dec(v_a_983_);
    return v_res_989_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(
    mut v_t_990_: *mut LeanObject,
    mut v_a_991_: *mut LeanObject,
    mut v_a_992_: *mut LeanObject,
    mut v_a_993_: *mut LeanObject,
    mut v_a_994_: *mut LeanObject,
    mut v_a_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1001_: u8 = 0;
    let mut v_val_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1005_: u8 = 0;
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1010_: u8 = 0;
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1017_: u8 = 0;
    let mut v_isSharedCheck_1018_: u8 = 0;
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1023_: u8 = 0;
    let mut v_a_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1027_: u8 = 0;
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_997_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(
                    v_t_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_,
                );
                if lean_obj_tag(v___x_997_) == 0 {
                    v_a_998_ = lean_ctor_get(v___x_997_, 0);
                    v_isSharedCheck_1023_ = (!lean_is_exclusive(v___x_997_)) as u8;
                    if v_isSharedCheck_1023_ == 0 {
                        v___x_1000_ = v___x_997_;
                        v_isShared_1001_ = v_isSharedCheck_1023_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_998_);
                        lean_dec(v___x_997_);
                        v___x_1000_ = lean_box(0);
                        v_isShared_1001_ = v_isSharedCheck_1023_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1024_ = lean_ctor_get(v___x_997_, 0);
                    v_isSharedCheck_1031_ = (!lean_is_exclusive(v___x_997_)) as u8;
                    if v_isSharedCheck_1031_ == 0 {
                        v___x_1026_ = v___x_997_;
                        v_isShared_1027_ = v_isSharedCheck_1031_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1024_);
                        lean_dec(v___x_997_);
                        v___x_1026_ = lean_box(0);
                        v_isShared_1027_ = v_isSharedCheck_1031_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_998_) == 1 {
                    lean_del_object(v___x_1000_);
                    v_val_1002_ = lean_ctor_get(v_a_998_, 0);
                    v_isSharedCheck_1018_ = (!lean_is_exclusive(v_a_998_)) as u8;
                    if v_isSharedCheck_1018_ == 0 {
                        v___x_1004_ = v_a_998_;
                        v_isShared_1005_ = v_isSharedCheck_1018_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1002_);
                        lean_dec(v_a_998_);
                        v___x_1004_ = lean_box(0);
                        v_isShared_1005_ = v_isSharedCheck_1018_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_998_);
                    v___x_1019_ = lean_box(0);
                    if v_isShared_1001_ == 0 {
                        lean_ctor_set(v___x_1000_, 0, v___x_1019_);
                        v___x_1021_ = v___x_1000_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
                        v___x_1021_ = v_reuseFailAlloc_1022_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1006_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_1002_);
                v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
                v_isSharedCheck_1017_ = (!lean_is_exclusive(v___x_1006_)) as u8;
                if v_isSharedCheck_1017_ == 0 {
                    v___x_1009_ = v___x_1006_;
                    v_isShared_1010_ = v_isSharedCheck_1017_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_1007_);
                    lean_dec(v___x_1006_);
                    v___x_1009_ = lean_box(0);
                    v_isShared_1010_ = v_isSharedCheck_1017_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1005_ == 0 {
                    lean_ctor_set(v___x_1004_, 0, v_a_1007_);
                    v___x_1012_ = v___x_1004_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1007_);
                    v___x_1012_ = v_reuseFailAlloc_1016_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1010_ == 0 {
                    lean_ctor_set(v___x_1009_, 0, v___x_1012_);
                    v___x_1014_ = v___x_1009_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1015_, 0, v___x_1012_);
                    v___x_1014_ = v_reuseFailAlloc_1015_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1014_;
            }
            6 => {
                return v___x_1021_;
            }
            7 => {
                if v_isShared_1027_ == 0 {
                    v___x_1029_ = v___x_1026_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
                    v___x_1029_ = v_reuseFailAlloc_1030_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom___boxed(
    mut v_t_1032_: *mut LeanObject,
    mut v_a_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1039_: *mut LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(
        v_t_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_,
    );
    lean_dec(v_a_1037_);
    lean_dec_ref(v_a_1036_);
    lean_dec(v_a_1035_);
    lean_dec_ref(v_a_1034_);
    lean_dec(v_a_1033_);
    return v_res_1039_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(
    mut v___x_1040_: *mut LeanObject,
    mut v___y_1041_: *mut LeanObject,
    mut v___y_1042_: *mut LeanObject,
    mut v___y_1043_: *mut LeanObject,
    mut v___y_1044_: *mut LeanObject,
    mut v___y_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    v___x_1047_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1047_, 0, v___x_1040_);
    return v___x_1047_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed(
    mut v___x_1048_: *mut LeanObject,
    mut v___y_1049_: *mut LeanObject,
    mut v___y_1050_: *mut LeanObject,
    mut v___y_1051_: *mut LeanObject,
    mut v___y_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1055_: *mut LeanObject = core::ptr::null_mut();
    v_res_1055_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(
        v___x_1048_,
        v___y_1049_,
        v___y_1050_,
        v___y_1051_,
        v___y_1052_,
        v___y_1053_,
    );
    lean_dec(v___y_1053_);
    lean_dec_ref(v___y_1052_);
    lean_dec(v___y_1051_);
    lean_dec_ref(v___y_1050_);
    lean_dec(v___y_1049_);
    return v_res_1055_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    v___x_1063_ = lean_box(0);
    v___x_1064_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1;
    v___x_1065_ = l_Lean_mkConst(v___x_1064_, v___x_1063_);
    return v___x_1065_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_box(0);
    v___x_1073_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5;
    v___x_1074_ = l_Lean_mkConst(v___x_1073_, v___x_1072_);
    return v___x_1074_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    v___x_1079_ = lean_box(0);
    v___x_1080_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8;
    v___x_1081_ = l_Lean_mkConst(v___x_1080_, v___x_1079_);
    return v___x_1081_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(
    mut v_val_1082_: u8,
) -> *mut LeanObject {
    let mut v_boolExpr_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_boolExpr_1084_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v_boolExpr_1084_, 0 as u32, v_val_1082_);
                v___x_1085_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2);
                v___x_1086_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6);
                if v_val_1082_ == 0 {
                    v___x_1093_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6);
                    v___y_1088_ = v___x_1093_;
                    state = 1;
                    continue;
                } else {
                    v___x_1094_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9);
                    v___y_1088_ = v___x_1094_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref_n(v___y_1088_, 2);
                v_expr_1089_ = l_Lean_mkAppB(v___x_1085_, v___x_1086_, v___y_1088_);
                v_proof_1090_ =
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3;
                v___x_1091_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1091_, 0, v_boolExpr_1084_);
                lean_ctor_set(v___x_1091_, 1, v___y_1088_);
                lean_ctor_set(v___x_1091_, 2, v_proof_1090_);
                lean_ctor_set(v___x_1091_, 3, v_expr_1089_);
                v___x_1092_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1092_, 0, v___x_1091_);
                return v___x_1092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___boxed(
    mut v_val_1095_: *mut LeanObject,
    mut v_a_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_1097_: u8 = 0;
    let mut v_res_1098_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_1097_ = (lean_unbox(v_val_1095_) as u8);
    v_res_1098_ =
        l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v_val_boxed_1097_);
    return v_res_1098_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(
    mut v_val_1099_: u8,
    mut v_a_1100_: *mut LeanObject,
    mut v_a_1101_: *mut LeanObject,
    mut v_a_1102_: *mut LeanObject,
    mut v_a_1103_: *mut LeanObject,
    mut v_a_1104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    v___x_1106_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v_val_1099_);
    return v___x_1106_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___boxed(
    mut v_val_1107_: *mut LeanObject,
    mut v_a_1108_: *mut LeanObject,
    mut v_a_1109_: *mut LeanObject,
    mut v_a_1110_: *mut LeanObject,
    mut v_a_1111_: *mut LeanObject,
    mut v_a_1112_: *mut LeanObject,
    mut v_a_1113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_1114_: u8 = 0;
    let mut v_res_1115_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_1114_ = (lean_unbox(v_val_1107_) as u8);
    v_res_1115_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(
        v_val_boxed_1114_,
        v_a_1108_,
        v_a_1109_,
        v_a_1110_,
        v_a_1111_,
        v_a_1112_,
    );
    lean_dec(v_a_1112_);
    lean_dec_ref(v_a_1111_);
    lean_dec(v_a_1110_);
    lean_dec_ref(v_a_1109_);
    lean_dec(v_a_1108_);
    return v_res_1115_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(
    mut v_gate_1149_: u8,
) -> *mut LeanObject {
    match v_gate_1149_ {
        0 => {
            let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
            v___x_1150_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2;
            return v___x_1150_;
        }
        1 => {
            let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
            v___x_1151_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4;
            return v___x_1151_;
        }
        2 => {
            let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
            v___x_1152_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6;
            return v___x_1152_;
        }
        _ => {
            let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
            v___x_1153_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8;
            return v___x_1153_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___boxed(
    mut v_gate_1154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_gate_boxed_1155_: u8 = 0;
    let mut v_res_1156_: *mut LeanObject = core::ptr::null_mut();
    v_gate_boxed_1155_ = (lean_unbox(v_gate_1154_) as u8);
    v_res_1156_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(v_gate_boxed_1155_);
    return v_res_1156_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(
    mut v_fst_1157_: *mut LeanObject,
    mut v_fproof_1158_: *mut LeanObject,
    mut v_snd_1159_: *mut LeanObject,
    mut v_sproof_1160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut v_val_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut v_val_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_fproof_1158_) == 0 {
                    lean_dec_ref(v_snd_1159_);
                    if lean_obj_tag(v_sproof_1160_) == 0 {
                        lean_dec_ref(v_fst_1157_);
                        v___x_1161_ = lean_box(0);
                        return v___x_1161_;
                    } else {
                        v_val_1162_ = lean_ctor_get(v_sproof_1160_, 0);
                        v_isSharedCheck_1171_ = (!lean_is_exclusive(v_sproof_1160_)) as u8;
                        if v_isSharedCheck_1171_ == 0 {
                            v___x_1164_ = v_sproof_1160_;
                            v_isShared_1165_ = v_isSharedCheck_1171_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1162_);
                            lean_dec(v_sproof_1160_);
                            v___x_1164_ = lean_box(0);
                            v_isShared_1165_ = v_isSharedCheck_1171_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fst_1157_);
                    if lean_obj_tag(v_sproof_1160_) == 0 {
                        v_val_1172_ = lean_ctor_get(v_fproof_1158_, 0);
                        v_isSharedCheck_1181_ = (!lean_is_exclusive(v_fproof_1158_)) as u8;
                        if v_isSharedCheck_1181_ == 0 {
                            v___x_1174_ = v_fproof_1158_;
                            v_isShared_1175_ = v_isSharedCheck_1181_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_1172_);
                            lean_dec(v_fproof_1158_);
                            v___x_1174_ = lean_box(0);
                            v_isShared_1175_ = v_isSharedCheck_1181_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_snd_1159_);
                        v_val_1182_ = lean_ctor_get(v_fproof_1158_, 0);
                        lean_inc(v_val_1182_);
                        lean_dec_ref_known(v_fproof_1158_, 1);
                        v_val_1183_ = lean_ctor_get(v_sproof_1160_, 0);
                        v_isSharedCheck_1191_ = (!lean_is_exclusive(v_sproof_1160_)) as u8;
                        if v_isSharedCheck_1191_ == 0 {
                            v___x_1185_ = v_sproof_1160_;
                            v_isShared_1186_ = v_isSharedCheck_1191_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_val_1183_);
                            lean_dec(v_sproof_1160_);
                            v___x_1185_ = lean_box(0);
                            v_isShared_1186_ = v_isSharedCheck_1191_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1166_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_fst_1157_);
                v___x_1167_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1167_, 0, v___x_1166_);
                lean_ctor_set(v___x_1167_, 1, v_val_1162_);
                if v_isShared_1165_ == 0 {
                    lean_ctor_set(v___x_1164_, 0, v___x_1167_);
                    v___x_1169_ = v___x_1164_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1167_);
                    v___x_1169_ = v_reuseFailAlloc_1170_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1169_;
            }
            3 => {
                v___x_1176_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_snd_1159_);
                v___x_1177_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1177_, 0, v_val_1172_);
                lean_ctor_set(v___x_1177_, 1, v___x_1176_);
                if v_isShared_1175_ == 0 {
                    lean_ctor_set(v___x_1174_, 0, v___x_1177_);
                    v___x_1179_ = v___x_1174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1180_, 0, v___x_1177_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1179_;
            }
            5 => {
                v___x_1187_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1187_, 0, v_val_1182_);
                lean_ctor_set(v___x_1187_, 1, v_val_1183_);
                if v_isShared_1186_ == 0 {
                    lean_ctor_set(v___x_1185_, 0, v___x_1187_);
                    v___x_1189_ = v___x_1185_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
                    v___x_1189_ = v_reuseFailAlloc_1190_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(
    mut v_expr_1192_: *mut LeanObject,
    mut v_expr_1193_: *mut LeanObject,
    mut v_lhs_1194_: *mut LeanObject,
    mut v_rhs_1195_: *mut LeanObject,
    mut v_congrThm_1196_: *mut LeanObject,
    mut v___x_1197_: *mut LeanObject,
    mut v_lhsExpr_1198_: *mut LeanObject,
    mut v_rhsExpr_1199_: *mut LeanObject,
    mut v___y_1200_: *mut LeanObject,
    mut v___y_1201_: *mut LeanObject,
    mut v___y_1202_: *mut LeanObject,
    mut v___y_1203_: *mut LeanObject,
    mut v___y_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1216_: u8 = 0;
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v_fst_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1237_: u8 = 0;
    let mut v_a_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1241_: u8 = 0;
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1245_: u8 = 0;
    let mut v_a_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1249_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1206_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                    v_expr_1192_,
                    v___y_1200_,
                    v___y_1201_,
                    v___y_1202_,
                    v___y_1203_,
                    v___y_1204_,
                );
                if lean_obj_tag(v___x_1206_) == 0 {
                    v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
                    lean_inc(v_a_1207_);
                    lean_dec_ref_known(v___x_1206_, 1);
                    v___x_1208_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                        v_expr_1193_,
                        v___y_1200_,
                        v___y_1201_,
                        v___y_1202_,
                        v___y_1203_,
                        v___y_1204_,
                    );
                    if lean_obj_tag(v___x_1208_) == 0 {
                        v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
                        lean_inc(v_a_1209_);
                        lean_dec_ref_known(v___x_1208_, 1);
                        v___x_1210_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                            v_lhs_1194_,
                            v___y_1200_,
                            v___y_1201_,
                            v___y_1202_,
                            v___y_1203_,
                            v___y_1204_,
                        );
                        if lean_obj_tag(v___x_1210_) == 0 {
                            v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
                            lean_inc(v_a_1211_);
                            lean_dec_ref_known(v___x_1210_, 1);
                            v___x_1212_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                                v_rhs_1195_,
                                v___y_1200_,
                                v___y_1201_,
                                v___y_1202_,
                                v___y_1203_,
                                v___y_1204_,
                            );
                            if lean_obj_tag(v___x_1212_) == 0 {
                                v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
                                v_isSharedCheck_1237_ = (!lean_is_exclusive(v___x_1212_)) as u8;
                                if v_isSharedCheck_1237_ == 0 {
                                    v___x_1215_ = v___x_1212_;
                                    v_isShared_1216_ = v_isSharedCheck_1237_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_1213_);
                                    lean_dec(v___x_1212_);
                                    v___x_1215_ = lean_box(0);
                                    v_isShared_1216_ = v_isSharedCheck_1237_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_1211_);
                                lean_dec(v_a_1209_);
                                lean_dec(v_a_1207_);
                                lean_dec_ref(v_rhsExpr_1199_);
                                lean_dec_ref(v_lhsExpr_1198_);
                                lean_dec(v___x_1197_);
                                lean_dec(v_congrThm_1196_);
                                return v___x_1212_;
                            }
                        } else {
                            lean_dec(v_a_1209_);
                            lean_dec(v_a_1207_);
                            lean_dec_ref(v_rhsExpr_1199_);
                            lean_dec_ref(v_lhsExpr_1198_);
                            lean_dec(v___x_1197_);
                            lean_dec(v_congrThm_1196_);
                            lean_dec_ref(v_rhs_1195_);
                            return v___x_1210_;
                        }
                    } else {
                        lean_dec(v_a_1207_);
                        lean_dec_ref(v_rhsExpr_1199_);
                        lean_dec_ref(v_lhsExpr_1198_);
                        lean_dec(v___x_1197_);
                        lean_dec(v_congrThm_1196_);
                        lean_dec_ref(v_rhs_1195_);
                        lean_dec_ref(v_lhs_1194_);
                        v_a_1238_ = lean_ctor_get(v___x_1208_, 0);
                        v_isSharedCheck_1245_ = (!lean_is_exclusive(v___x_1208_)) as u8;
                        if v_isSharedCheck_1245_ == 0 {
                            v___x_1240_ = v___x_1208_;
                            v_isShared_1241_ = v_isSharedCheck_1245_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1238_);
                            lean_dec(v___x_1208_);
                            v___x_1240_ = lean_box(0);
                            v_isShared_1241_ = v_isSharedCheck_1245_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhsExpr_1199_);
                    lean_dec_ref(v_lhsExpr_1198_);
                    lean_dec(v___x_1197_);
                    lean_dec(v_congrThm_1196_);
                    lean_dec_ref(v_rhs_1195_);
                    lean_dec_ref(v_lhs_1194_);
                    lean_dec_ref(v_expr_1193_);
                    v_a_1246_ = lean_ctor_get(v___x_1206_, 0);
                    v_isSharedCheck_1253_ = (!lean_is_exclusive(v___x_1206_)) as u8;
                    if v_isSharedCheck_1253_ == 0 {
                        v___x_1248_ = v___x_1206_;
                        v_isShared_1249_ = v_isSharedCheck_1253_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_1246_);
                        lean_dec(v___x_1206_);
                        v___x_1248_ = lean_box(0);
                        v_isShared_1249_ = v_isSharedCheck_1253_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_1209_);
                lean_inc(v_a_1207_);
                v___x_1217_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_a_1207_, v_a_1211_, v_a_1209_, v_a_1213_);
                if lean_obj_tag(v___x_1217_) == 1 {
                    v_val_1218_ = lean_ctor_get(v___x_1217_, 0);
                    v_isSharedCheck_1232_ = (!lean_is_exclusive(v___x_1217_)) as u8;
                    if v_isSharedCheck_1232_ == 0 {
                        v___x_1220_ = v___x_1217_;
                        v_isShared_1221_ = v_isSharedCheck_1232_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1218_);
                        lean_dec(v___x_1217_);
                        v___x_1220_ = lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1232_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1217_);
                    lean_dec(v_a_1209_);
                    lean_dec(v_a_1207_);
                    lean_dec_ref(v_rhsExpr_1199_);
                    lean_dec_ref(v_lhsExpr_1198_);
                    lean_dec(v___x_1197_);
                    lean_dec(v_congrThm_1196_);
                    v___x_1233_ = lean_box(0);
                    if v_isShared_1216_ == 0 {
                        lean_ctor_set(v___x_1215_, 0, v___x_1233_);
                        v___x_1235_ = v___x_1215_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1236_, 0, v___x_1233_);
                        v___x_1235_ = v_reuseFailAlloc_1236_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_1222_ = lean_ctor_get(v_val_1218_, 0);
                lean_inc(v_fst_1222_);
                v_snd_1223_ = lean_ctor_get(v_val_1218_, 1);
                lean_inc(v_snd_1223_);
                lean_dec(v_val_1218_);
                v___x_1224_ = l_Lean_mkConst(v_congrThm_1196_, v___x_1197_);
                v___x_1225_ = l_Lean_mkApp6(
                    v___x_1224_,
                    v_lhsExpr_1198_,
                    v_rhsExpr_1199_,
                    v_a_1207_,
                    v_a_1209_,
                    v_fst_1222_,
                    v_snd_1223_,
                );
                if v_isShared_1221_ == 0 {
                    lean_ctor_set(v___x_1220_, 0, v___x_1225_);
                    v___x_1227_ = v___x_1220_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1225_);
                    v___x_1227_ = v_reuseFailAlloc_1231_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1216_ == 0 {
                    lean_ctor_set(v___x_1215_, 0, v___x_1227_);
                    v___x_1229_ = v___x_1215_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
                    v___x_1229_ = v_reuseFailAlloc_1230_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1229_;
            }
            5 => {
                return v___x_1235_;
            }
            6 => {
                if v_isShared_1241_ == 0 {
                    v___x_1243_ = v___x_1240_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
                    v___x_1243_ = v_reuseFailAlloc_1244_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1243_;
            }
            8 => {
                if v_isShared_1249_ == 0 {
                    v___x_1251_ = v___x_1248_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
                    v___x_1251_ = v_reuseFailAlloc_1252_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed(
    mut v_expr_1254_: *mut LeanObject,
    mut v_expr_1255_: *mut LeanObject,
    mut v_lhs_1256_: *mut LeanObject,
    mut v_rhs_1257_: *mut LeanObject,
    mut v_congrThm_1258_: *mut LeanObject,
    mut v___x_1259_: *mut LeanObject,
    mut v_lhsExpr_1260_: *mut LeanObject,
    mut v_rhsExpr_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
    mut v___y_1264_: *mut LeanObject,
    mut v___y_1265_: *mut LeanObject,
    mut v___y_1266_: *mut LeanObject,
    mut v___y_1267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1268_: *mut LeanObject = core::ptr::null_mut();
    v_res_1268_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(
        v_expr_1254_,
        v_expr_1255_,
        v_lhs_1256_,
        v_rhs_1257_,
        v_congrThm_1258_,
        v___x_1259_,
        v_lhsExpr_1260_,
        v_rhsExpr_1261_,
        v___y_1262_,
        v___y_1263_,
        v___y_1264_,
        v___y_1265_,
        v___y_1266_,
    );
    lean_dec(v___y_1266_);
    lean_dec_ref(v___y_1265_);
    lean_dec(v___y_1264_);
    lean_dec_ref(v___y_1263_);
    lean_dec(v___y_1262_);
    return v_res_1268_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1276_ = lean_box(0);
    v___x_1277_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1;
    v___x_1278_ = l_Lean_mkConst(v___x_1277_, v___x_1276_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1287_ = lean_box(0);
    v___x_1288_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5;
    v___x_1289_ = l_Lean_mkConst(v___x_1288_, v___x_1287_);
    return v___x_1289_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v___x_1297_ = lean_box(0);
    v___x_1298_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8;
    v___x_1299_ = l_Lean_mkConst(v___x_1298_, v___x_1297_);
    return v___x_1299_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307_ = lean_box(0);
    v___x_1308_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11;
    v___x_1309_ = l_Lean_mkConst(v___x_1308_, v___x_1307_);
    return v___x_1309_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    v___x_1317_ = lean_box(0);
    v___x_1318_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14;
    v___x_1319_ = l_Lean_mkConst(v___x_1318_, v___x_1317_);
    return v___x_1319_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(
    mut v_lhs_1320_: *mut LeanObject,
    mut v_rhs_1321_: *mut LeanObject,
    mut v_lhsExpr_1322_: *mut LeanObject,
    mut v_rhsExpr_1323_: *mut LeanObject,
    mut v_gate_1324_: u8,
    mut v_origExpr_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bvExpr_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrThm_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_boolExpr_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_bvExpr_1327_ = lean_ctor_get(v_lhs_1320_, 0);
                v_expr_1328_ = lean_ctor_get(v_lhs_1320_, 3);
                lean_inc_ref_n(v_expr_1328_, 2);
                v_bvExpr_1329_ = lean_ctor_get(v_rhs_1321_, 0);
                v_expr_1330_ = lean_ctor_get(v_rhs_1321_, 3);
                lean_inc_ref_n(v_expr_1330_, 2);
                v_congrThm_1331_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(v_gate_1324_);
                lean_inc_ref(v_bvExpr_1329_);
                lean_inc_ref(v_bvExpr_1327_);
                v_boolExpr_1332_ = lean_alloc_ctor(3, 2, (1) as u32);
                lean_ctor_set(v_boolExpr_1332_, 0, v_bvExpr_1327_);
                lean_ctor_set(v_boolExpr_1332_, 1, v_bvExpr_1329_);
                lean_ctor_set_uint8(
                    v_boolExpr_1332_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_gate_1324_,
                );
                v___x_1333_ = lean_box(0);
                v_proof_1334_ = lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    14,
                    8,
                );
                lean_closure_set(v_proof_1334_, 0, v_expr_1328_);
                lean_closure_set(v_proof_1334_, 1, v_expr_1330_);
                lean_closure_set(v_proof_1334_, 2, v_lhs_1320_);
                lean_closure_set(v_proof_1334_, 3, v_rhs_1321_);
                lean_closure_set(v_proof_1334_, 4, v_congrThm_1331_);
                lean_closure_set(v_proof_1334_, 5, v___x_1333_);
                lean_closure_set(v_proof_1334_, 6, v_lhsExpr_1322_);
                lean_closure_set(v_proof_1334_, 7, v_rhsExpr_1323_);
                v___x_1335_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2);
                v___x_1336_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6);
                match v_gate_1324_ {
                    0 => {
                        v___x_1342_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6);
                        v___y_1338_ = v___x_1342_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_1343_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9);
                        v___y_1338_ = v___x_1343_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v___x_1344_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12);
                        v___y_1338_ = v___x_1344_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_1345_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15_once), _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15);
                        v___y_1338_ = v___x_1345_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_1338_);
                v_expr_1339_ = l_Lean_mkApp4(
                    v___x_1335_,
                    v___x_1336_,
                    v___y_1338_,
                    v_expr_1328_,
                    v_expr_1330_,
                );
                v___x_1340_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1340_, 0, v_boolExpr_1332_);
                lean_ctor_set(v___x_1340_, 1, v_origExpr_1325_);
                lean_ctor_set(v___x_1340_, 2, v_proof_1334_);
                lean_ctor_set(v___x_1340_, 3, v_expr_1339_);
                v___x_1341_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1341_, 0, v___x_1340_);
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___boxed(
    mut v_lhs_1346_: *mut LeanObject,
    mut v_rhs_1347_: *mut LeanObject,
    mut v_lhsExpr_1348_: *mut LeanObject,
    mut v_rhsExpr_1349_: *mut LeanObject,
    mut v_gate_1350_: *mut LeanObject,
    mut v_origExpr_1351_: *mut LeanObject,
    mut v_a_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_gate_boxed_1353_: u8 = 0;
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
    v_gate_boxed_1353_ = (lean_unbox(v_gate_1350_) as u8);
    v_res_1354_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(
        v_lhs_1346_,
        v_rhs_1347_,
        v_lhsExpr_1348_,
        v_rhsExpr_1349_,
        v_gate_boxed_1353_,
        v_origExpr_1351_,
    );
    return v_res_1354_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(
    mut v_lhs_1355_: *mut LeanObject,
    mut v_rhs_1356_: *mut LeanObject,
    mut v_lhsExpr_1357_: *mut LeanObject,
    mut v_rhsExpr_1358_: *mut LeanObject,
    mut v_gate_1359_: u8,
    mut v_origExpr_1360_: *mut LeanObject,
    mut v_a_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
    mut v_a_1363_: *mut LeanObject,
    mut v_a_1364_: *mut LeanObject,
    mut v_a_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(
        v_lhs_1355_,
        v_rhs_1356_,
        v_lhsExpr_1357_,
        v_rhsExpr_1358_,
        v_gate_1359_,
        v_origExpr_1360_,
    );
    return v___x_1367_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___boxed(
    mut v_lhs_1368_: *mut LeanObject,
    mut v_rhs_1369_: *mut LeanObject,
    mut v_lhsExpr_1370_: *mut LeanObject,
    mut v_rhsExpr_1371_: *mut LeanObject,
    mut v_gate_1372_: *mut LeanObject,
    mut v_origExpr_1373_: *mut LeanObject,
    mut v_a_1374_: *mut LeanObject,
    mut v_a_1375_: *mut LeanObject,
    mut v_a_1376_: *mut LeanObject,
    mut v_a_1377_: *mut LeanObject,
    mut v_a_1378_: *mut LeanObject,
    mut v_a_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_gate_boxed_1380_: u8 = 0;
    let mut v_res_1381_: *mut LeanObject = core::ptr::null_mut();
    v_gate_boxed_1380_ = (lean_unbox(v_gate_1372_) as u8);
    v_res_1381_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(
        v_lhs_1368_,
        v_rhs_1369_,
        v_lhsExpr_1370_,
        v_rhsExpr_1371_,
        v_gate_boxed_1380_,
        v_origExpr_1373_,
        v_a_1374_,
        v_a_1375_,
        v_a_1376_,
        v_a_1377_,
        v_a_1378_,
    );
    lean_dec(v_a_1378_);
    lean_dec_ref(v_a_1377_);
    lean_dec(v_a_1376_);
    lean_dec_ref(v_a_1375_);
    lean_dec(v_a_1374_);
    return v_res_1381_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(
    mut v_sub_1383_: *mut LeanObject,
    mut v_expr_1384_: *mut LeanObject,
    mut v___x_1385_: *mut LeanObject,
    mut v___x_1386_: *mut LeanObject,
    mut v___x_1387_: *mut LeanObject,
    mut v___x_1388_: *mut LeanObject,
    mut v_subExpr_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
    mut v___y_1394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1400_: u8 = 0;
    let mut v_val_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut v_a_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1426_: u8 = 0;
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1430_: u8 = 0;
    let mut v_isSharedCheck_1431_: u8 = 0;
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1396_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                    v_sub_1383_,
                    v___y_1390_,
                    v___y_1391_,
                    v___y_1392_,
                    v___y_1393_,
                    v___y_1394_,
                );
                if lean_obj_tag(v___x_1396_) == 0 {
                    v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
                    v_isSharedCheck_1436_ = (!lean_is_exclusive(v___x_1396_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v___x_1399_ = v___x_1396_;
                        v_isShared_1400_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1397_);
                        lean_dec(v___x_1396_);
                        v___x_1399_ = lean_box(0);
                        v_isShared_1400_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_subExpr_1389_);
                    lean_dec(v___x_1388_);
                    lean_dec_ref(v___x_1387_);
                    lean_dec_ref(v___x_1386_);
                    lean_dec_ref(v___x_1385_);
                    lean_dec_ref(v_expr_1384_);
                    return v___x_1396_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1397_) == 1 {
                    lean_del_object(v___x_1399_);
                    v_val_1401_ = lean_ctor_get(v_a_1397_, 0);
                    v_isSharedCheck_1431_ = (!lean_is_exclusive(v_a_1397_)) as u8;
                    if v_isSharedCheck_1431_ == 0 {
                        v___x_1403_ = v_a_1397_;
                        v_isShared_1404_ = v_isSharedCheck_1431_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1401_);
                        lean_dec(v_a_1397_);
                        v___x_1403_ = lean_box(0);
                        v_isShared_1404_ = v_isSharedCheck_1431_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1397_);
                    lean_dec_ref(v_subExpr_1389_);
                    lean_dec(v___x_1388_);
                    lean_dec_ref(v___x_1387_);
                    lean_dec_ref(v___x_1386_);
                    lean_dec_ref(v___x_1385_);
                    lean_dec_ref(v_expr_1384_);
                    v___x_1432_ = lean_box(0);
                    if v_isShared_1400_ == 0 {
                        lean_ctor_set(v___x_1399_, 0, v___x_1432_);
                        v___x_1434_ = v___x_1399_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
                        v___x_1434_ = v_reuseFailAlloc_1435_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1405_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                    v_expr_1384_,
                    v___y_1390_,
                    v___y_1391_,
                    v___y_1392_,
                    v___y_1393_,
                    v___y_1394_,
                );
                if lean_obj_tag(v___x_1405_) == 0 {
                    v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
                    v_isSharedCheck_1422_ = (!lean_is_exclusive(v___x_1405_)) as u8;
                    if v_isSharedCheck_1422_ == 0 {
                        v___x_1408_ = v___x_1405_;
                        v_isShared_1409_ = v_isSharedCheck_1422_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1406_);
                        lean_dec(v___x_1405_);
                        v___x_1408_ = lean_box(0);
                        v_isShared_1409_ = v_isSharedCheck_1422_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1403_);
                    lean_dec(v_val_1401_);
                    lean_dec_ref(v_subExpr_1389_);
                    lean_dec(v___x_1388_);
                    lean_dec_ref(v___x_1387_);
                    lean_dec_ref(v___x_1386_);
                    lean_dec_ref(v___x_1385_);
                    v_a_1423_ = lean_ctor_get(v___x_1405_, 0);
                    v_isSharedCheck_1430_ = (!lean_is_exclusive(v___x_1405_)) as u8;
                    if v_isSharedCheck_1430_ == 0 {
                        v___x_1425_ = v___x_1405_;
                        v_isShared_1426_ = v_isSharedCheck_1430_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1423_);
                        lean_dec(v___x_1405_);
                        v___x_1425_ = lean_box(0);
                        v_isShared_1426_ = v_isSharedCheck_1430_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1410_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0;
                v___x_1411_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6;
                v___x_1412_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0;
                v___x_1413_ = l_Lean_Name_mkStr6(
                    v___x_1385_,
                    v___x_1386_,
                    v___x_1387_,
                    v___x_1410_,
                    v___x_1411_,
                    v___x_1412_,
                );
                v___x_1414_ = l_Lean_mkConst(v___x_1413_, v___x_1388_);
                v___x_1415_ = l_Lean_mkApp3(v___x_1414_, v_subExpr_1389_, v_a_1406_, v_val_1401_);
                if v_isShared_1404_ == 0 {
                    lean_ctor_set(v___x_1403_, 0, v___x_1415_);
                    v___x_1417_ = v___x_1403_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1415_);
                    v___x_1417_ = v_reuseFailAlloc_1421_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1409_ == 0 {
                    lean_ctor_set(v___x_1408_, 0, v___x_1417_);
                    v___x_1419_ = v___x_1408_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
                    v___x_1419_ = v_reuseFailAlloc_1420_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1419_;
            }
            6 => {
                if v_isShared_1426_ == 0 {
                    v___x_1428_ = v___x_1425_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1429_, 0, v_a_1423_);
                    v___x_1428_ = v_reuseFailAlloc_1429_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1428_;
            }
            8 => {
                return v___x_1434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed(
    mut v_sub_1437_: *mut LeanObject,
    mut v_expr_1438_: *mut LeanObject,
    mut v___x_1439_: *mut LeanObject,
    mut v___x_1440_: *mut LeanObject,
    mut v___x_1441_: *mut LeanObject,
    mut v___x_1442_: *mut LeanObject,
    mut v_subExpr_1443_: *mut LeanObject,
    mut v___y_1444_: *mut LeanObject,
    mut v___y_1445_: *mut LeanObject,
    mut v___y_1446_: *mut LeanObject,
    mut v___y_1447_: *mut LeanObject,
    mut v___y_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1450_: *mut LeanObject = core::ptr::null_mut();
    v_res_1450_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(
        v_sub_1437_,
        v_expr_1438_,
        v___x_1439_,
        v___x_1440_,
        v___x_1441_,
        v___x_1442_,
        v_subExpr_1443_,
        v___y_1444_,
        v___y_1445_,
        v___y_1446_,
        v___y_1447_,
        v___y_1448_,
    );
    lean_dec(v___y_1448_);
    lean_dec_ref(v___y_1447_);
    lean_dec(v___y_1446_);
    lean_dec_ref(v___y_1445_);
    lean_dec(v___y_1444_);
    return v_res_1450_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    v___x_1458_ = lean_box(0);
    v___x_1459_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1;
    v___x_1460_ = l_Lean_mkConst(v___x_1459_, v___x_1458_);
    return v___x_1460_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(
    mut v_sub_1461_: *mut LeanObject,
    mut v_subExpr_1462_: *mut LeanObject,
    mut v_origExpr_1463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bvExpr_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_boolExpr_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    v_bvExpr_1465_ = lean_ctor_get(v_sub_1461_, 0);
    v_expr_1466_ = lean_ctor_get(v_sub_1461_, 3);
    lean_inc_ref_n(v_expr_1466_, 2);
    lean_inc_ref(v_bvExpr_1465_);
    v_boolExpr_1467_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v_boolExpr_1467_, 0, v_bvExpr_1465_);
    v___x_1468_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0;
    v___x_1469_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1;
    v___x_1470_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2;
    v___x_1471_ = lean_box(0);
    v_proof_1472_ = lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        7,
    );
    lean_closure_set(v_proof_1472_, 0, v_sub_1461_);
    lean_closure_set(v_proof_1472_, 1, v_expr_1466_);
    lean_closure_set(v_proof_1472_, 2, v___x_1468_);
    lean_closure_set(v_proof_1472_, 3, v___x_1469_);
    lean_closure_set(v_proof_1472_, 4, v___x_1470_);
    lean_closure_set(v_proof_1472_, 5, v___x_1471_);
    lean_closure_set(v_proof_1472_, 6, v_subExpr_1462_);
    v___x_1473_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2,
    );
    v___x_1474_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6,
    );
    v_expr_1475_ = l_Lean_mkAppB(v___x_1473_, v___x_1474_, v_expr_1466_);
    v___x_1476_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1476_, 0, v_boolExpr_1467_);
    lean_ctor_set(v___x_1476_, 1, v_origExpr_1463_);
    lean_ctor_set(v___x_1476_, 2, v_proof_1472_);
    lean_ctor_set(v___x_1476_, 3, v_expr_1475_);
    v___x_1477_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1477_, 0, v___x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___boxed(
    mut v_sub_1478_: *mut LeanObject,
    mut v_subExpr_1479_: *mut LeanObject,
    mut v_origExpr_1480_: *mut LeanObject,
    mut v_a_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1482_: *mut LeanObject = core::ptr::null_mut();
    v_res_1482_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(
        v_sub_1478_,
        v_subExpr_1479_,
        v_origExpr_1480_,
    );
    return v_res_1482_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(
    mut v_sub_1483_: *mut LeanObject,
    mut v_subExpr_1484_: *mut LeanObject,
    mut v_origExpr_1485_: *mut LeanObject,
    mut v_a_1486_: *mut LeanObject,
    mut v_a_1487_: *mut LeanObject,
    mut v_a_1488_: *mut LeanObject,
    mut v_a_1489_: *mut LeanObject,
    mut v_a_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1492_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(
        v_sub_1483_,
        v_subExpr_1484_,
        v_origExpr_1485_,
    );
    return v___x_1492_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___boxed(
    mut v_sub_1493_: *mut LeanObject,
    mut v_subExpr_1494_: *mut LeanObject,
    mut v_origExpr_1495_: *mut LeanObject,
    mut v_a_1496_: *mut LeanObject,
    mut v_a_1497_: *mut LeanObject,
    mut v_a_1498_: *mut LeanObject,
    mut v_a_1499_: *mut LeanObject,
    mut v_a_1500_: *mut LeanObject,
    mut v_a_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1502_: *mut LeanObject = core::ptr::null_mut();
    v_res_1502_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(
        v_sub_1493_,
        v_subExpr_1494_,
        v_origExpr_1495_,
        v_a_1496_,
        v_a_1497_,
        v_a_1498_,
        v_a_1499_,
        v_a_1500_,
    );
    lean_dec(v_a_1500_);
    lean_dec_ref(v_a_1499_);
    lean_dec(v_a_1498_);
    lean_dec_ref(v_a_1497_);
    lean_dec(v_a_1496_);
    return v_res_1502_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(
    mut v_fst_1503_: *mut LeanObject,
    mut v_fproof_1504_: *mut LeanObject,
    mut v_snd_1505_: *mut LeanObject,
    mut v_sproof_1506_: *mut LeanObject,
    mut v_thd_1507_: *mut LeanObject,
    mut v_tproof_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1520_: u8 = 0;
    let mut v_val_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_fproof_1504_) == 0 {
                    v___x_1509_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_snd_1505_, v_sproof_1506_, v_thd_1507_, v_tproof_1508_);
                    if lean_obj_tag(v___x_1509_) == 0 {
                        lean_dec_ref(v_fst_1503_);
                        v___x_1510_ = lean_box(0);
                        return v___x_1510_;
                    } else {
                        v_val_1511_ = lean_ctor_get(v___x_1509_, 0);
                        v_isSharedCheck_1520_ = (!lean_is_exclusive(v___x_1509_)) as u8;
                        if v_isSharedCheck_1520_ == 0 {
                            v___x_1513_ = v___x_1509_;
                            v_isShared_1514_ = v_isSharedCheck_1520_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1511_);
                            lean_dec(v___x_1509_);
                            v___x_1513_ = lean_box(0);
                            v_isShared_1514_ = v_isSharedCheck_1520_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_fst_1503_);
                    v_val_1521_ = lean_ctor_get(v_fproof_1504_, 0);
                    v_isSharedCheck_1542_ = (!lean_is_exclusive(v_fproof_1504_)) as u8;
                    if v_isSharedCheck_1542_ == 0 {
                        v___x_1523_ = v_fproof_1504_;
                        v_isShared_1524_ = v_isSharedCheck_1542_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1521_);
                        lean_dec(v_fproof_1504_);
                        v___x_1523_ = lean_box(0);
                        v_isShared_1524_ = v_isSharedCheck_1542_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1515_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_fst_1503_);
                v___x_1516_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1516_, 0, v___x_1515_);
                lean_ctor_set(v___x_1516_, 1, v_val_1511_);
                if v_isShared_1514_ == 0 {
                    lean_ctor_set(v___x_1513_, 0, v___x_1516_);
                    v___x_1518_ = v___x_1513_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
                    v___x_1518_ = v_reuseFailAlloc_1519_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1518_;
            }
            3 => {
                lean_inc_ref(v_thd_1507_);
                lean_inc_ref(v_snd_1505_);
                v___x_1525_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_snd_1505_, v_sproof_1506_, v_thd_1507_, v_tproof_1508_);
                if lean_obj_tag(v___x_1525_) == 0 {
                    v___x_1526_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_snd_1505_);
                    v___x_1527_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_thd_1507_);
                    v___x_1528_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1528_, 0, v___x_1526_);
                    lean_ctor_set(v___x_1528_, 1, v___x_1527_);
                    v___x_1529_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1529_, 0, v_val_1521_);
                    lean_ctor_set(v___x_1529_, 1, v___x_1528_);
                    if v_isShared_1524_ == 0 {
                        lean_ctor_set(v___x_1523_, 0, v___x_1529_);
                        v___x_1531_ = v___x_1523_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
                        v___x_1531_ = v_reuseFailAlloc_1532_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1523_);
                    lean_dec_ref(v_thd_1507_);
                    lean_dec_ref(v_snd_1505_);
                    v_val_1533_ = lean_ctor_get(v___x_1525_, 0);
                    v_isSharedCheck_1541_ = (!lean_is_exclusive(v___x_1525_)) as u8;
                    if v_isSharedCheck_1541_ == 0 {
                        v___x_1535_ = v___x_1525_;
                        v_isShared_1536_ = v_isSharedCheck_1541_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_1533_);
                        lean_dec(v___x_1525_);
                        v___x_1535_ = lean_box(0);
                        v_isShared_1536_ = v_isSharedCheck_1541_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1531_;
            }
            5 => {
                v___x_1537_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1537_, 0, v_val_1521_);
                lean_ctor_set(v___x_1537_, 1, v_val_1533_);
                if v_isShared_1536_ == 0 {
                    lean_ctor_set(v___x_1535_, 0, v___x_1537_);
                    v___x_1539_ = v___x_1535_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
                    v___x_1539_ = v_reuseFailAlloc_1540_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(
    mut v_expr_1544_: *mut LeanObject,
    mut v_expr_1545_: *mut LeanObject,
    mut v_expr_1546_: *mut LeanObject,
    mut v_discr_1547_: *mut LeanObject,
    mut v_lhs_1548_: *mut LeanObject,
    mut v_rhs_1549_: *mut LeanObject,
    mut v___x_1550_: *mut LeanObject,
    mut v___x_1551_: *mut LeanObject,
    mut v___x_1552_: *mut LeanObject,
    mut v___x_1553_: *mut LeanObject,
    mut v_discrExpr_1554_: *mut LeanObject,
    mut v_lhsExpr_1555_: *mut LeanObject,
    mut v_rhsExpr_1556_: *mut LeanObject,
    mut v___y_1557_: *mut LeanObject,
    mut v___y_1558_: *mut LeanObject,
    mut v___y_1559_: *mut LeanObject,
    mut v___y_1560_: *mut LeanObject,
    mut v___y_1561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v_snd_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1599_: u8 = 0;
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1604_: u8 = 0;
    let mut v_a_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1608_: u8 = 0;
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1563_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                    v_expr_1544_,
                    v___y_1557_,
                    v___y_1558_,
                    v___y_1559_,
                    v___y_1560_,
                    v___y_1561_,
                );
                if lean_obj_tag(v___x_1563_) == 0 {
                    v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
                    lean_inc(v_a_1564_);
                    lean_dec_ref_known(v___x_1563_, 1);
                    v___x_1565_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                        v_expr_1545_,
                        v___y_1557_,
                        v___y_1558_,
                        v___y_1559_,
                        v___y_1560_,
                        v___y_1561_,
                    );
                    if lean_obj_tag(v___x_1565_) == 0 {
                        v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
                        lean_inc(v_a_1566_);
                        lean_dec_ref_known(v___x_1565_, 1);
                        v___x_1567_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                            v_expr_1546_,
                            v___y_1557_,
                            v___y_1558_,
                            v___y_1559_,
                            v___y_1560_,
                            v___y_1561_,
                        );
                        if lean_obj_tag(v___x_1567_) == 0 {
                            v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
                            lean_inc(v_a_1568_);
                            lean_dec_ref_known(v___x_1567_, 1);
                            v___x_1569_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                                v_discr_1547_,
                                v___y_1557_,
                                v___y_1558_,
                                v___y_1559_,
                                v___y_1560_,
                                v___y_1561_,
                            );
                            if lean_obj_tag(v___x_1569_) == 0 {
                                v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
                                lean_inc(v_a_1570_);
                                lean_dec_ref_known(v___x_1569_, 1);
                                v___x_1571_ =
                                    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                                        v_lhs_1548_,
                                        v___y_1557_,
                                        v___y_1558_,
                                        v___y_1559_,
                                        v___y_1560_,
                                        v___y_1561_,
                                    );
                                if lean_obj_tag(v___x_1571_) == 0 {
                                    v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
                                    lean_inc(v_a_1572_);
                                    lean_dec_ref_known(v___x_1571_, 1);
                                    v___x_1573_ =
                                        l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                                            v_rhs_1549_,
                                            v___y_1557_,
                                            v___y_1558_,
                                            v___y_1559_,
                                            v___y_1560_,
                                            v___y_1561_,
                                        );
                                    if lean_obj_tag(v___x_1573_) == 0 {
                                        v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
                                        v_isSharedCheck_1604_ =
                                            (!lean_is_exclusive(v___x_1573_)) as u8;
                                        if v_isSharedCheck_1604_ == 0 {
                                            v___x_1576_ = v___x_1573_;
                                            v_isShared_1577_ = v_isSharedCheck_1604_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1574_);
                                            lean_dec(v___x_1573_);
                                            v___x_1576_ = lean_box(0);
                                            v_isShared_1577_ = v_isSharedCheck_1604_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_1572_);
                                        lean_dec(v_a_1570_);
                                        lean_dec(v_a_1568_);
                                        lean_dec(v_a_1566_);
                                        lean_dec(v_a_1564_);
                                        lean_dec_ref(v_rhsExpr_1556_);
                                        lean_dec_ref(v_lhsExpr_1555_);
                                        lean_dec_ref(v_discrExpr_1554_);
                                        lean_dec(v___x_1553_);
                                        lean_dec_ref(v___x_1552_);
                                        lean_dec_ref(v___x_1551_);
                                        lean_dec_ref(v___x_1550_);
                                        return v___x_1573_;
                                    }
                                } else {
                                    lean_dec(v_a_1570_);
                                    lean_dec(v_a_1568_);
                                    lean_dec(v_a_1566_);
                                    lean_dec(v_a_1564_);
                                    lean_dec_ref(v_rhsExpr_1556_);
                                    lean_dec_ref(v_lhsExpr_1555_);
                                    lean_dec_ref(v_discrExpr_1554_);
                                    lean_dec(v___x_1553_);
                                    lean_dec_ref(v___x_1552_);
                                    lean_dec_ref(v___x_1551_);
                                    lean_dec_ref(v___x_1550_);
                                    lean_dec_ref(v_rhs_1549_);
                                    return v___x_1571_;
                                }
                            } else {
                                lean_dec(v_a_1568_);
                                lean_dec(v_a_1566_);
                                lean_dec(v_a_1564_);
                                lean_dec_ref(v_rhsExpr_1556_);
                                lean_dec_ref(v_lhsExpr_1555_);
                                lean_dec_ref(v_discrExpr_1554_);
                                lean_dec(v___x_1553_);
                                lean_dec_ref(v___x_1552_);
                                lean_dec_ref(v___x_1551_);
                                lean_dec_ref(v___x_1550_);
                                lean_dec_ref(v_rhs_1549_);
                                lean_dec_ref(v_lhs_1548_);
                                return v___x_1569_;
                            }
                        } else {
                            lean_dec(v_a_1566_);
                            lean_dec(v_a_1564_);
                            lean_dec_ref(v_rhsExpr_1556_);
                            lean_dec_ref(v_lhsExpr_1555_);
                            lean_dec_ref(v_discrExpr_1554_);
                            lean_dec(v___x_1553_);
                            lean_dec_ref(v___x_1552_);
                            lean_dec_ref(v___x_1551_);
                            lean_dec_ref(v___x_1550_);
                            lean_dec_ref(v_rhs_1549_);
                            lean_dec_ref(v_lhs_1548_);
                            lean_dec_ref(v_discr_1547_);
                            v_a_1605_ = lean_ctor_get(v___x_1567_, 0);
                            v_isSharedCheck_1612_ = (!lean_is_exclusive(v___x_1567_)) as u8;
                            if v_isSharedCheck_1612_ == 0 {
                                v___x_1607_ = v___x_1567_;
                                v_isShared_1608_ = v_isSharedCheck_1612_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_1605_);
                                lean_dec(v___x_1567_);
                                v___x_1607_ = lean_box(0);
                                v_isShared_1608_ = v_isSharedCheck_1612_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1564_);
                        lean_dec_ref(v_rhsExpr_1556_);
                        lean_dec_ref(v_lhsExpr_1555_);
                        lean_dec_ref(v_discrExpr_1554_);
                        lean_dec(v___x_1553_);
                        lean_dec_ref(v___x_1552_);
                        lean_dec_ref(v___x_1551_);
                        lean_dec_ref(v___x_1550_);
                        lean_dec_ref(v_rhs_1549_);
                        lean_dec_ref(v_lhs_1548_);
                        lean_dec_ref(v_discr_1547_);
                        lean_dec_ref(v_expr_1546_);
                        v_a_1613_ = lean_ctor_get(v___x_1565_, 0);
                        v_isSharedCheck_1620_ = (!lean_is_exclusive(v___x_1565_)) as u8;
                        if v_isSharedCheck_1620_ == 0 {
                            v___x_1615_ = v___x_1565_;
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1613_);
                            lean_dec(v___x_1565_);
                            v___x_1615_ = lean_box(0);
                            v_isShared_1616_ = v_isSharedCheck_1620_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rhsExpr_1556_);
                    lean_dec_ref(v_lhsExpr_1555_);
                    lean_dec_ref(v_discrExpr_1554_);
                    lean_dec(v___x_1553_);
                    lean_dec_ref(v___x_1552_);
                    lean_dec_ref(v___x_1551_);
                    lean_dec_ref(v___x_1550_);
                    lean_dec_ref(v_rhs_1549_);
                    lean_dec_ref(v_lhs_1548_);
                    lean_dec_ref(v_discr_1547_);
                    lean_dec_ref(v_expr_1546_);
                    lean_dec_ref(v_expr_1545_);
                    v_a_1621_ = lean_ctor_get(v___x_1563_, 0);
                    v_isSharedCheck_1628_ = (!lean_is_exclusive(v___x_1563_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1623_ = v___x_1563_;
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1621_);
                        lean_dec(v___x_1563_);
                        v___x_1623_ = lean_box(0);
                        v_isShared_1624_ = v_isSharedCheck_1628_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_1568_);
                lean_inc(v_a_1566_);
                lean_inc(v_a_1564_);
                v___x_1578_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(v_a_1564_, v_a_1570_, v_a_1566_, v_a_1572_, v_a_1568_, v_a_1574_);
                if lean_obj_tag(v___x_1578_) == 1 {
                    v_val_1579_ = lean_ctor_get(v___x_1578_, 0);
                    v_isSharedCheck_1599_ = (!lean_is_exclusive(v___x_1578_)) as u8;
                    if v_isSharedCheck_1599_ == 0 {
                        v___x_1581_ = v___x_1578_;
                        v_isShared_1582_ = v_isSharedCheck_1599_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1579_);
                        lean_dec(v___x_1578_);
                        v___x_1581_ = lean_box(0);
                        v_isShared_1582_ = v_isSharedCheck_1599_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1578_);
                    lean_dec(v_a_1568_);
                    lean_dec(v_a_1566_);
                    lean_dec(v_a_1564_);
                    lean_dec_ref(v_rhsExpr_1556_);
                    lean_dec_ref(v_lhsExpr_1555_);
                    lean_dec_ref(v_discrExpr_1554_);
                    lean_dec(v___x_1553_);
                    lean_dec_ref(v___x_1552_);
                    lean_dec_ref(v___x_1551_);
                    lean_dec_ref(v___x_1550_);
                    v___x_1600_ = lean_box(0);
                    if v_isShared_1577_ == 0 {
                        lean_ctor_set(v___x_1576_, 0, v___x_1600_);
                        v___x_1602_ = v___x_1576_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
                        v___x_1602_ = v_reuseFailAlloc_1603_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_1583_ = lean_ctor_get(v_val_1579_, 1);
                lean_inc(v_snd_1583_);
                v_fst_1584_ = lean_ctor_get(v_val_1579_, 0);
                lean_inc(v_fst_1584_);
                lean_dec(v_val_1579_);
                v_fst_1585_ = lean_ctor_get(v_snd_1583_, 0);
                lean_inc(v_fst_1585_);
                v_snd_1586_ = lean_ctor_get(v_snd_1583_, 1);
                lean_inc(v_snd_1586_);
                lean_dec(v_snd_1583_);
                v___x_1587_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0;
                v___x_1588_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6;
                v___x_1589_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0;
                v___x_1590_ = l_Lean_Name_mkStr6(
                    v___x_1550_,
                    v___x_1551_,
                    v___x_1552_,
                    v___x_1587_,
                    v___x_1588_,
                    v___x_1589_,
                );
                v___x_1591_ = l_Lean_mkConst(v___x_1590_, v___x_1553_);
                v___x_1592_ = l_Lean_mkApp9(
                    v___x_1591_,
                    v_discrExpr_1554_,
                    v_lhsExpr_1555_,
                    v_rhsExpr_1556_,
                    v_a_1564_,
                    v_a_1566_,
                    v_a_1568_,
                    v_fst_1584_,
                    v_fst_1585_,
                    v_snd_1586_,
                );
                if v_isShared_1582_ == 0 {
                    lean_ctor_set(v___x_1581_, 0, v___x_1592_);
                    v___x_1594_ = v___x_1581_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1592_);
                    v___x_1594_ = v_reuseFailAlloc_1598_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1577_ == 0 {
                    lean_ctor_set(v___x_1576_, 0, v___x_1594_);
                    v___x_1596_ = v___x_1576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1594_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1596_;
            }
            5 => {
                return v___x_1602_;
            }
            6 => {
                if v_isShared_1608_ == 0 {
                    v___x_1610_ = v___x_1607_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
                    v___x_1610_ = v_reuseFailAlloc_1611_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1610_;
            }
            8 => {
                if v_isShared_1616_ == 0 {
                    v___x_1618_ = v___x_1615_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1618_;
            }
            10 => {
                if v_isShared_1624_ == 0 {
                    v___x_1626_ = v___x_1623_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
                    v___x_1626_ = v_reuseFailAlloc_1627_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_1629_: *mut LeanObject = *_args.add(0);
    let mut v_expr_1630_: *mut LeanObject = *_args.add(1);
    let mut v_expr_1631_: *mut LeanObject = *_args.add(2);
    let mut v_discr_1632_: *mut LeanObject = *_args.add(3);
    let mut v_lhs_1633_: *mut LeanObject = *_args.add(4);
    let mut v_rhs_1634_: *mut LeanObject = *_args.add(5);
    let mut v___x_1635_: *mut LeanObject = *_args.add(6);
    let mut v___x_1636_: *mut LeanObject = *_args.add(7);
    let mut v___x_1637_: *mut LeanObject = *_args.add(8);
    let mut v___x_1638_: *mut LeanObject = *_args.add(9);
    let mut v_discrExpr_1639_: *mut LeanObject = *_args.add(10);
    let mut v_lhsExpr_1640_: *mut LeanObject = *_args.add(11);
    let mut v_rhsExpr_1641_: *mut LeanObject = *_args.add(12);
    let mut v___y_1642_: *mut LeanObject = *_args.add(13);
    let mut v___y_1643_: *mut LeanObject = *_args.add(14);
    let mut v___y_1644_: *mut LeanObject = *_args.add(15);
    let mut v___y_1645_: *mut LeanObject = *_args.add(16);
    let mut v___y_1646_: *mut LeanObject = *_args.add(17);
    let mut v___y_1647_: *mut LeanObject = *_args.add(18);
    let mut v_res_1648_: *mut LeanObject = core::ptr::null_mut();
    v_res_1648_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(
        v_expr_1629_,
        v_expr_1630_,
        v_expr_1631_,
        v_discr_1632_,
        v_lhs_1633_,
        v_rhs_1634_,
        v___x_1635_,
        v___x_1636_,
        v___x_1637_,
        v___x_1638_,
        v_discrExpr_1639_,
        v_lhsExpr_1640_,
        v_rhsExpr_1641_,
        v___y_1642_,
        v___y_1643_,
        v___y_1644_,
        v___y_1645_,
        v___y_1646_,
    );
    lean_dec(v___y_1646_);
    lean_dec_ref(v___y_1645_);
    lean_dec(v___y_1644_);
    lean_dec_ref(v___y_1643_);
    lean_dec(v___y_1642_);
    return v_res_1648_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1656_ = lean_box(0);
    v___x_1657_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1;
    v___x_1658_ = l_Lean_mkConst(v___x_1657_, v___x_1656_);
    return v___x_1658_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(
    mut v_discr_1659_: *mut LeanObject,
    mut v_lhs_1660_: *mut LeanObject,
    mut v_rhs_1661_: *mut LeanObject,
    mut v_discrExpr_1662_: *mut LeanObject,
    mut v_lhsExpr_1663_: *mut LeanObject,
    mut v_rhsExpr_1664_: *mut LeanObject,
    mut v_origExpr_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bvExpr_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_boolExpr_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    v_bvExpr_1667_ = lean_ctor_get(v_discr_1659_, 0);
    v_expr_1668_ = lean_ctor_get(v_discr_1659_, 3);
    lean_inc_ref_n(v_expr_1668_, 2);
    v_bvExpr_1669_ = lean_ctor_get(v_lhs_1660_, 0);
    v_expr_1670_ = lean_ctor_get(v_lhs_1660_, 3);
    lean_inc_ref_n(v_expr_1670_, 2);
    v_bvExpr_1671_ = lean_ctor_get(v_rhs_1661_, 0);
    v_expr_1672_ = lean_ctor_get(v_rhs_1661_, 3);
    lean_inc_ref_n(v_expr_1672_, 2);
    lean_inc_ref(v_bvExpr_1671_);
    lean_inc_ref(v_bvExpr_1669_);
    lean_inc_ref(v_bvExpr_1667_);
    v_boolExpr_1673_ = lean_alloc_ctor(4, 3, (0) as u32);
    lean_ctor_set(v_boolExpr_1673_, 0, v_bvExpr_1667_);
    lean_ctor_set(v_boolExpr_1673_, 1, v_bvExpr_1669_);
    lean_ctor_set(v_boolExpr_1673_, 2, v_bvExpr_1671_);
    v___x_1674_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0;
    v___x_1675_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1;
    v___x_1676_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2;
    v___x_1677_ = lean_box(0);
    v_proof_1678_ = lean_alloc_closure(
        l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        19,
        13,
    );
    lean_closure_set(v_proof_1678_, 0, v_expr_1668_);
    lean_closure_set(v_proof_1678_, 1, v_expr_1670_);
    lean_closure_set(v_proof_1678_, 2, v_expr_1672_);
    lean_closure_set(v_proof_1678_, 3, v_discr_1659_);
    lean_closure_set(v_proof_1678_, 4, v_lhs_1660_);
    lean_closure_set(v_proof_1678_, 5, v_rhs_1661_);
    lean_closure_set(v_proof_1678_, 6, v___x_1674_);
    lean_closure_set(v_proof_1678_, 7, v___x_1675_);
    lean_closure_set(v_proof_1678_, 8, v___x_1676_);
    lean_closure_set(v_proof_1678_, 9, v___x_1677_);
    lean_closure_set(v_proof_1678_, 10, v_discrExpr_1662_);
    lean_closure_set(v_proof_1678_, 11, v_lhsExpr_1663_);
    lean_closure_set(v_proof_1678_, 12, v_rhsExpr_1664_);
    v___x_1679_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2,
    );
    v___x_1680_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once
        ),
        _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6,
    );
    v_expr_1681_ = l_Lean_mkApp4(
        v___x_1679_,
        v___x_1680_,
        v_expr_1668_,
        v_expr_1670_,
        v_expr_1672_,
    );
    v___x_1682_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1682_, 0, v_boolExpr_1673_);
    lean_ctor_set(v___x_1682_, 1, v_origExpr_1665_);
    lean_ctor_set(v___x_1682_, 2, v_proof_1678_);
    lean_ctor_set(v___x_1682_, 3, v_expr_1681_);
    v___x_1683_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1683_, 0, v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___boxed(
    mut v_discr_1684_: *mut LeanObject,
    mut v_lhs_1685_: *mut LeanObject,
    mut v_rhs_1686_: *mut LeanObject,
    mut v_discrExpr_1687_: *mut LeanObject,
    mut v_lhsExpr_1688_: *mut LeanObject,
    mut v_rhsExpr_1689_: *mut LeanObject,
    mut v_origExpr_1690_: *mut LeanObject,
    mut v_a_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1692_: *mut LeanObject = core::ptr::null_mut();
    v_res_1692_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(
        v_discr_1684_,
        v_lhs_1685_,
        v_rhs_1686_,
        v_discrExpr_1687_,
        v_lhsExpr_1688_,
        v_rhsExpr_1689_,
        v_origExpr_1690_,
    );
    return v_res_1692_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(
    mut v_discr_1693_: *mut LeanObject,
    mut v_lhs_1694_: *mut LeanObject,
    mut v_rhs_1695_: *mut LeanObject,
    mut v_discrExpr_1696_: *mut LeanObject,
    mut v_lhsExpr_1697_: *mut LeanObject,
    mut v_rhsExpr_1698_: *mut LeanObject,
    mut v_origExpr_1699_: *mut LeanObject,
    mut v_a_1700_: *mut LeanObject,
    mut v_a_1701_: *mut LeanObject,
    mut v_a_1702_: *mut LeanObject,
    mut v_a_1703_: *mut LeanObject,
    mut v_a_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(
        v_discr_1693_,
        v_lhs_1694_,
        v_rhs_1695_,
        v_discrExpr_1696_,
        v_lhsExpr_1697_,
        v_rhsExpr_1698_,
        v_origExpr_1699_,
    );
    return v___x_1706_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___boxed(
    mut v_discr_1707_: *mut LeanObject,
    mut v_lhs_1708_: *mut LeanObject,
    mut v_rhs_1709_: *mut LeanObject,
    mut v_discrExpr_1710_: *mut LeanObject,
    mut v_lhsExpr_1711_: *mut LeanObject,
    mut v_rhsExpr_1712_: *mut LeanObject,
    mut v_origExpr_1713_: *mut LeanObject,
    mut v_a_1714_: *mut LeanObject,
    mut v_a_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
    mut v_a_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: *mut LeanObject = core::ptr::null_mut();
    v_res_1720_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(
        v_discr_1707_,
        v_lhs_1708_,
        v_rhs_1709_,
        v_discrExpr_1710_,
        v_lhsExpr_1711_,
        v_rhsExpr_1712_,
        v_origExpr_1713_,
        v_a_1714_,
        v_a_1715_,
        v_a_1716_,
        v_a_1717_,
        v_a_1718_,
    );
    lean_dec(v_a_1718_);
    lean_dec_ref(v_a_1717_);
    lean_dec(v_a_1716_);
    lean_dec_ref(v_a_1715_);
    lean_dec(v_a_1714_);
    return v_res_1720_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
}
