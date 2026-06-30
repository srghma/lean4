// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Focus
// Imports: Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::ffi::{
    lean_expr_dbg_to_string, lean_name_eq, lean_panic_fn_borrowed, lean_st_ref_get,
    lean_string_append,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal, l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21, l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo,
    l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp, l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_mkApp6, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData};
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value
        ) as *mut leanh::LeanObject,
        17542774118954891045 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value:
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
    m_data: [70, 111, 99, 117, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value:
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
    m_data: [116, 104, 105, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut leanh::LeanObject,
        18104247681175793831 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut leanh::LeanObject,
        280574599804500352 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_4)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value)
            as *mut leanh::LeanObject,
        17031249732047591641 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value:
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
    m_data: [108, 101, 102, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut leanh::LeanObject,
        18104247681175793831 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut leanh::LeanObject,
        280574599804500352 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_4)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value)
            as *mut leanh::LeanObject,
        15785676217249922417 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value:
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
    m_data: [114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut leanh::LeanObject,
        18104247681175793831 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_3)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut leanh::LeanObject,
        280574599804500352 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_4)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value)
            as *mut leanh::LeanObject,
        2568375699356494615 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11_value:
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 70, 111, 99, 117, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80,
        114, 111, 111, 102, 77, 111, 100, 101, 46, 102, 111, 99, 117, 115, 72, 121, 112, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13_value:
    leanh::LeanStringObject<47> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        102, 111, 99, 117, 115, 72, 121, 112, 58, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105,
        115, 32, 119, 105, 116, 104, 111, 117, 116, 32, 112, 114, 111, 112, 101, 114, 32, 109, 101,
        116, 97, 100, 97, 116, 97, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value)
            as *mut leanh::LeanObject,
        8550510443043304393 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value)
            as *mut leanh::LeanObject,
        14477891125163417350 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value:
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
    m_data: [114, 101, 119, 114, 105, 116, 101, 95, 104, 121, 112, 115, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut leanh::LeanObject,
        15734321041234825264 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut leanh::LeanObject,
        7300584325018775040 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut leanh::LeanObject,
        13332341187416043682 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut leanh::LeanObject,
        18104247681175793831 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_4:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut leanh::LeanObject,
        280574599804500352 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_4
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value
        ) as *mut leanh::LeanObject,
        14389574595038836286 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        105, 109, 112, 111, 115, 115, 105, 98, 108, 101, 59, 32, 114, 101, 115, 46, 102, 111, 99,
        117, 115, 72, 121, 112, 32, 110, 111, 116, 32, 97, 32, 104, 121, 112, 111, 116, 104, 101,
        115, 105, 115, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115,
        32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = leanh::lean_box(0);
    v___x_375_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1;
    v___x_376_ = l_Lean_Expr_const___override(v___x_375_, v___x_374_);
    return v___x_376_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2,
    );
    v___x_378_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_378_, 0, v___x_377_);
    leanh::lean_ctor_set(v___x_378_, 1, v___x_377_);
    leanh::lean_ctor_set(v___x_378_, 2, v___x_377_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default()
-> *mut leanh::LeanObject {
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3,
    );
    return v___x_379_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult()
-> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default;
    return v___x_380_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_focusHyp_spec__0(
    mut v_msg_381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = leanh::lean_box(0);
    v___x_383_ = lean_panic_fn_borrowed(v___x_382_, v_msg_381_);
    return v___x_383_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
    mut v_u_416_: *mut leanh::LeanObject,
    mut v_00_u03c3s_417_: *mut leanh::LeanObject,
    mut v_e_418_: *mut leanh::LeanObject,
    mut v_name_419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v_name_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_428_: u8 = 0;
    let mut v___x_429_: u8 = 0;
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_443_: u8 = 0;
    let mut v_unused_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_446_: u8 = 0;
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_460_: u8 = 0;
    let mut v_focusHyp_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut v_val_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v_focusHyp_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_518_: u8 = 0;
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_418_);
                v___x_420_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_418_);
                if leanh::lean_obj_tag(v___x_420_) == 1 {
                    v_val_421_ = leanh::lean_ctor_get(v___x_420_, 0);
                    v_isSharedCheck_446_ = (!leanh::lean_is_exclusive(v___x_420_)) as u8;
                    if v_isSharedCheck_446_ == 0 {
                        v___x_423_ = v___x_420_;
                        v_isShared_424_ = v_isSharedCheck_446_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_421_);
                        leanh::lean_dec(v___x_420_);
                        v___x_423_ = leanh::lean_box(0);
                        v_isShared_424_ = v_isSharedCheck_446_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_420_);
                    leanh::lean_dec_ref(v_00_u03c3s_417_);
                    leanh::lean_dec(v_u_416_);
                    v___x_447_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_418_);
                    if leanh::lean_obj_tag(v___x_447_) == 1 {
                        leanh::lean_dec_ref(v_e_418_);
                        v_val_448_ = leanh::lean_ctor_get(v___x_447_, 0);
                        leanh::lean_inc(v_val_448_);
                        leanh::lean_dec_ref_known(v___x_447_, 1);
                        v_snd_449_ = leanh::lean_ctor_get(v_val_448_, 1);
                        leanh::lean_inc(v_snd_449_);
                        v_snd_450_ = leanh::lean_ctor_get(v_snd_449_, 1);
                        leanh::lean_inc(v_snd_450_);
                        v_fst_451_ = leanh::lean_ctor_get(v_val_448_, 0);
                        leanh::lean_inc_n(v_fst_451_, 2);
                        leanh::lean_dec(v_val_448_);
                        v_fst_452_ = leanh::lean_ctor_get(v_snd_449_, 0);
                        leanh::lean_inc_n(v_fst_452_, 2);
                        leanh::lean_dec(v_snd_449_);
                        v_fst_453_ = leanh::lean_ctor_get(v_snd_450_, 0);
                        leanh::lean_inc(v_fst_453_);
                        v_snd_454_ = leanh::lean_ctor_get(v_snd_450_, 1);
                        leanh::lean_inc_n(v_snd_454_, 2);
                        leanh::lean_dec(v_snd_450_);
                        v___x_455_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
                            v_fst_451_,
                            v_fst_452_,
                            v_snd_454_,
                            v_name_419_,
                        );
                        if leanh::lean_obj_tag(v___x_455_) == 0 {
                            leanh::lean_inc(v_fst_453_);
                            leanh::lean_inc(v_fst_452_);
                            leanh::lean_inc(v_fst_451_);
                            v___x_456_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
                                v_fst_451_,
                                v_fst_452_,
                                v_fst_453_,
                                v_name_419_,
                            );
                            if leanh::lean_obj_tag(v___x_456_) == 0 {
                                leanh::lean_dec(v_snd_454_);
                                leanh::lean_dec(v_fst_453_);
                                leanh::lean_dec(v_fst_452_);
                                leanh::lean_dec(v_fst_451_);
                                return v___x_456_;
                            } else {
                                v_val_457_ = leanh::lean_ctor_get(v___x_456_, 0);
                                v_isSharedCheck_488_ =
                                    (!leanh::lean_is_exclusive(v___x_456_)) as u8;
                                if v_isSharedCheck_488_ == 0 {
                                    v___x_459_ = v___x_456_;
                                    v_isShared_460_ = v_isSharedCheck_488_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_457_);
                                    leanh::lean_dec(v___x_456_);
                                    v___x_459_ = leanh::lean_box(0);
                                    v_isShared_460_ = v_isSharedCheck_488_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_val_489_ = leanh::lean_ctor_get(v___x_455_, 0);
                            v_isSharedCheck_520_ =
                                (!leanh::lean_is_exclusive(v___x_455_)) as u8;
                            if v_isSharedCheck_520_ == 0 {
                                v___x_491_ = v___x_455_;
                                v_isShared_492_ = v_isSharedCheck_520_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_489_);
                                leanh::lean_dec(v___x_455_);
                                v___x_491_ = leanh::lean_box(0);
                                v_isShared_492_ = v_isSharedCheck_520_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_447_);
                        leanh::lean_inc_ref(v_e_418_);
                        v___x_521_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_418_);
                        if leanh::lean_obj_tag(v___x_521_) == 1 {
                            leanh::lean_dec_ref_known(v___x_521_, 1);
                            leanh::lean_dec_ref(v_e_418_);
                            v___x_522_ = leanh::lean_box(0);
                            return v___x_522_;
                        } else {
                            leanh::lean_dec(v___x_521_);
                            v___x_523_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11;
                            v___x_524_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12;
                            v___x_525_ = leanh::lean_unsigned_to_nat(46);
                            v___x_526_ = leanh::lean_unsigned_to_nat(4);
                            v___x_527_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13;
                            v___x_528_ = lean_expr_dbg_to_string(v_e_418_);
                            leanh::lean_dec_ref(v_e_418_);
                            v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
                            leanh::lean_dec_ref(v___x_528_);
                            v___x_530_ = l_mkPanicMessageWithDecl(
                                v___x_523_, v___x_524_, v___x_525_, v___x_526_, v___x_529_,
                            );
                            leanh::lean_dec_ref(v___x_529_);
                            v___x_531_ =
                                l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_focusHyp_spec__0(
                                    v___x_530_,
                                );
                            return v___x_531_;
                        }
                    }
                }
            }
            1 => {
                v_name_425_ = leanh::lean_ctor_get(v_val_421_, 0);
                v_isSharedCheck_443_ = (!leanh::lean_is_exclusive(v_val_421_)) as u8;
                if v_isSharedCheck_443_ == 0 {
                    v_unused_444_ = leanh::lean_ctor_get(v_val_421_, 2);
                    leanh::lean_dec(v_unused_444_);
                    v_unused_445_ = leanh::lean_ctor_get(v_val_421_, 1);
                    leanh::lean_dec(v_unused_445_);
                    v___x_427_ = v_val_421_;
                    v_isShared_428_ = v_isSharedCheck_443_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_name_425_);
                    leanh::lean_dec(v_val_421_);
                    v___x_427_ = leanh::lean_box(0);
                    v_isShared_428_ = v_isSharedCheck_443_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_429_ = lean_name_eq(v_name_425_, v_name_419_);
                leanh::lean_dec(v_name_425_);
                if v___x_429_ == 0 {
                    leanh::lean_del_object(v___x_427_);
                    leanh::lean_del_object(v___x_423_);
                    leanh::lean_dec_ref(v_e_418_);
                    leanh::lean_dec_ref(v_00_u03c3s_417_);
                    leanh::lean_dec(v_u_416_);
                    v___x_430_ = leanh::lean_box(0);
                    return v___x_430_;
                } else {
                    leanh::lean_inc_ref(v_00_u03c3s_417_);
                    leanh::lean_inc(v_u_416_);
                    v___x_431_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_416_, v_00_u03c3s_417_);
                    v___x_432_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6;
                    v___x_433_ = leanh::lean_box(0);
                    v___x_434_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_434_, 0, v_u_416_);
                    leanh::lean_ctor_set(v___x_434_, 1, v___x_433_);
                    v___x_435_ = l_Lean_mkConst(v___x_432_, v___x_434_);
                    leanh::lean_inc_ref(v_e_418_);
                    v___x_436_ = l_Lean_mkAppB(v___x_435_, v_00_u03c3s_417_, v_e_418_);
                    if v_isShared_428_ == 0 {
                        leanh::lean_ctor_set(v___x_427_, 2, v___x_436_);
                        leanh::lean_ctor_set(v___x_427_, 1, v___x_431_);
                        leanh::lean_ctor_set(v___x_427_, 0, v_e_418_);
                        v___x_438_ = v___x_427_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_442_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_442_, 0, v_e_418_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_431_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_442_, 2, v___x_436_);
                        v___x_438_ = v_reuseFailAlloc_442_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_424_ == 0 {
                    leanh::lean_ctor_set(v___x_423_, 0, v___x_438_);
                    v___x_440_ = v___x_423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
                    v___x_440_ = v_reuseFailAlloc_441_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_440_;
            }
            5 => {
                v_focusHyp_461_ = leanh::lean_ctor_get(v_val_457_, 0);
                v_restHyps_462_ = leanh::lean_ctor_get(v_val_457_, 1);
                v_proof_463_ = leanh::lean_ctor_get(v_val_457_, 2);
                v_isSharedCheck_487_ = (!leanh::lean_is_exclusive(v_val_457_)) as u8;
                if v_isSharedCheck_487_ == 0 {
                    v___x_465_ = v_val_457_;
                    v_isShared_466_ = v_isSharedCheck_487_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_proof_463_);
                    leanh::lean_inc(v_restHyps_462_);
                    leanh::lean_inc(v_focusHyp_461_);
                    leanh::lean_dec(v_val_457_);
                    v___x_465_ = leanh::lean_box(0);
                    v_isShared_466_ = v_isSharedCheck_487_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc(v_snd_454_);
                leanh::lean_inc_ref(v_restHyps_462_);
                leanh::lean_inc(v_fst_452_);
                leanh::lean_inc(v_fst_451_);
                v___x_467_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_fst_451_,
                    v_fst_452_,
                    v_restHyps_462_,
                    v_snd_454_,
                );
                v_fst_468_ = leanh::lean_ctor_get(v___x_467_, 0);
                v_snd_469_ = leanh::lean_ctor_get(v___x_467_, 1);
                v_isSharedCheck_486_ = (!leanh::lean_is_exclusive(v___x_467_)) as u8;
                if v_isSharedCheck_486_ == 0 {
                    v___x_471_ = v___x_467_;
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_469_);
                    leanh::lean_inc(v_fst_468_);
                    leanh::lean_dec(v___x_467_);
                    v___x_471_ = leanh::lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_473_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8;
                v___x_474_ = leanh::lean_box(0);
                if v_isShared_472_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_471_, 1);
                    leanh::lean_ctor_set(v___x_471_, 1, v___x_474_);
                    leanh::lean_ctor_set(v___x_471_, 0, v_fst_451_);
                    v___x_476_ = v___x_471_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_485_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fst_451_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_474_);
                    v___x_476_ = v_reuseFailAlloc_485_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_477_ = l_Lean_mkConst(v___x_473_, v___x_476_);
                leanh::lean_inc_ref(v_focusHyp_461_);
                leanh::lean_inc(v_fst_468_);
                v___x_478_ = l_Lean_mkApp8(
                    v___x_477_,
                    v_fst_452_,
                    v_fst_453_,
                    v_restHyps_462_,
                    v_snd_454_,
                    v_fst_468_,
                    v_focusHyp_461_,
                    v_proof_463_,
                    v_snd_469_,
                );
                if v_isShared_466_ == 0 {
                    leanh::lean_ctor_set(v___x_465_, 2, v___x_478_);
                    leanh::lean_ctor_set(v___x_465_, 1, v_fst_468_);
                    v___x_480_ = v___x_465_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_484_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_484_, 0, v_focusHyp_461_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_484_, 1, v_fst_468_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_484_, 2, v___x_478_);
                    v___x_480_ = v_reuseFailAlloc_484_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_460_ == 0 {
                    leanh::lean_ctor_set(v___x_459_, 0, v___x_480_);
                    v___x_482_ = v___x_459_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
                    v___x_482_ = v_reuseFailAlloc_483_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_482_;
            }
            11 => {
                v_focusHyp_493_ = leanh::lean_ctor_get(v_val_489_, 0);
                v_restHyps_494_ = leanh::lean_ctor_get(v_val_489_, 1);
                v_proof_495_ = leanh::lean_ctor_get(v_val_489_, 2);
                v_isSharedCheck_519_ = (!leanh::lean_is_exclusive(v_val_489_)) as u8;
                if v_isSharedCheck_519_ == 0 {
                    v___x_497_ = v_val_489_;
                    v_isShared_498_ = v_isSharedCheck_519_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_proof_495_);
                    leanh::lean_inc(v_restHyps_494_);
                    leanh::lean_inc(v_focusHyp_493_);
                    leanh::lean_dec(v_val_489_);
                    v___x_497_ = leanh::lean_box(0);
                    v_isShared_498_ = v_isSharedCheck_519_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                leanh::lean_inc_ref(v_restHyps_494_);
                leanh::lean_inc(v_fst_453_);
                leanh::lean_inc(v_fst_452_);
                leanh::lean_inc(v_fst_451_);
                v___x_499_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_fst_451_,
                    v_fst_452_,
                    v_fst_453_,
                    v_restHyps_494_,
                );
                v_fst_500_ = leanh::lean_ctor_get(v___x_499_, 0);
                v_snd_501_ = leanh::lean_ctor_get(v___x_499_, 1);
                v_isSharedCheck_518_ = (!leanh::lean_is_exclusive(v___x_499_)) as u8;
                if v_isSharedCheck_518_ == 0 {
                    v___x_503_ = v___x_499_;
                    v_isShared_504_ = v_isSharedCheck_518_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_501_);
                    leanh::lean_inc(v_fst_500_);
                    leanh::lean_dec(v___x_499_);
                    v___x_503_ = leanh::lean_box(0);
                    v_isShared_504_ = v_isSharedCheck_518_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_505_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10;
                v___x_506_ = leanh::lean_box(0);
                if v_isShared_504_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_503_, 1);
                    leanh::lean_ctor_set(v___x_503_, 1, v___x_506_);
                    leanh::lean_ctor_set(v___x_503_, 0, v_fst_451_);
                    v___x_508_ = v___x_503_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_517_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_517_, 0, v_fst_451_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_506_);
                    v___x_508_ = v_reuseFailAlloc_517_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_509_ = l_Lean_mkConst(v___x_505_, v___x_508_);
                leanh::lean_inc_ref(v_focusHyp_493_);
                leanh::lean_inc(v_fst_500_);
                v___x_510_ = l_Lean_mkApp8(
                    v___x_509_,
                    v_fst_452_,
                    v_fst_453_,
                    v_snd_454_,
                    v_restHyps_494_,
                    v_fst_500_,
                    v_focusHyp_493_,
                    v_proof_495_,
                    v_snd_501_,
                );
                if v_isShared_498_ == 0 {
                    leanh::lean_ctor_set(v___x_497_, 2, v___x_510_);
                    leanh::lean_ctor_set(v___x_497_, 1, v_fst_500_);
                    v___x_512_ = v___x_497_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_516_, 0, v_focusHyp_493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_516_, 1, v_fst_500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_516_, 2, v___x_510_);
                    v___x_512_ = v_reuseFailAlloc_516_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_492_ == 0 {
                    leanh::lean_ctor_set(v___x_491_, 0, v___x_512_);
                    v___x_514_ = v___x_491_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_515_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
                    v___x_514_ = v_reuseFailAlloc_515_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___boxed(
    mut v_u_532_: *mut leanh::LeanObject,
    mut v_00_u03c3s_533_: *mut leanh::LeanObject,
    mut v_e_534_: *mut leanh::LeanObject,
    mut v_name_535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_536_ =
        l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_u_532_, v_00_u03c3s_533_, v_e_534_, v_name_535_);
    leanh::lean_dec(v_name_535_);
    return v_res_536_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(
    mut v_goal_537_: *mut leanh::LeanObject,
    mut v_name_538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_u_539_ = leanh::lean_ctor_get(v_goal_537_, 0);
    leanh::lean_inc(v_u_539_);
    v_00_u03c3s_540_ = leanh::lean_ctor_get(v_goal_537_, 1);
    leanh::lean_inc_ref(v_00_u03c3s_540_);
    v_hyps_541_ = leanh::lean_ctor_get(v_goal_537_, 2);
    leanh::lean_inc_ref(v_hyps_541_);
    leanh::lean_dec_ref(v_goal_537_);
    v___x_542_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
        v_u_539_,
        v_00_u03c3s_540_,
        v_hyps_541_,
        v_name_538_,
    );
    return v___x_542_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp___boxed(
    mut v_goal_543_: *mut leanh::LeanObject,
    mut v_name_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_goal_543_, v_name_544_);
    leanh::lean_dec(v_name_544_);
    return v_res_545_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl(
    mut v_u_554_: *mut leanh::LeanObject,
    mut v_00_u03c3s_555_: *mut leanh::LeanObject,
    mut v_restHyps_556_: *mut leanh::LeanObject,
    mut v_focusHyp_557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2;
    v___x_559_ = leanh::lean_box(0);
    leanh::lean_inc(v_u_554_);
    v___x_560_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_560_, 0, v_u_554_);
    leanh::lean_ctor_set(v___x_560_, 1, v___x_559_);
    v___x_561_ = l_Lean_mkConst(v___x_558_, v___x_560_);
    leanh::lean_inc_ref(v_focusHyp_557_);
    leanh::lean_inc_ref(v_restHyps_556_);
    leanh::lean_inc_ref(v_00_u03c3s_555_);
    v___x_562_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
        v_u_554_,
        v_00_u03c3s_555_,
        v_restHyps_556_,
        v_focusHyp_557_,
    );
    v_proof_563_ = l_Lean_mkAppB(v___x_561_, v_00_u03c3s_555_, v___x_562_);
    v___x_564_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_564_, 0, v_focusHyp_557_);
    leanh::lean_ctor_set(v___x_564_, 1, v_restHyps_556_);
    leanh::lean_ctor_set(v___x_564_, 2, v_proof_563_);
    return v___x_564_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(
    mut v_res_565_: *mut leanh::LeanObject,
    mut v_goal_566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v_restHyps_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut v_unused_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_567_ = leanh::lean_ctor_get(v_goal_566_, 0);
                v_00_u03c3s_568_ = leanh::lean_ctor_get(v_goal_566_, 1);
                v_target_569_ = leanh::lean_ctor_get(v_goal_566_, 3);
                v_isSharedCheck_577_ = (!leanh::lean_is_exclusive(v_goal_566_)) as u8;
                if v_isSharedCheck_577_ == 0 {
                    v_unused_578_ = leanh::lean_ctor_get(v_goal_566_, 2);
                    leanh::lean_dec(v_unused_578_);
                    v___x_571_ = v_goal_566_;
                    v_isShared_572_ = v_isSharedCheck_577_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_target_569_);
                    leanh::lean_inc(v_00_u03c3s_568_);
                    leanh::lean_inc(v_u_567_);
                    leanh::lean_dec(v_goal_566_);
                    v___x_571_ = leanh::lean_box(0);
                    v_isShared_572_ = v_isSharedCheck_577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_restHyps_573_ = leanh::lean_ctor_get(v_res_565_, 1);
                leanh::lean_inc_ref(v_restHyps_573_);
                if v_isShared_572_ == 0 {
                    leanh::lean_ctor_set(v___x_571_, 2, v_restHyps_573_);
                    v___x_575_ = v___x_571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_576_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 0, v_u_567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 1, v_00_u03c3s_568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 2, v_restHyps_573_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_576_, 3, v_target_569_);
                    v___x_575_ = v_reuseFailAlloc_576_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal___boxed(
    mut v_res_579_: *mut leanh::LeanObject,
    mut v_goal_580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_res_579_, v_goal_580_);
    leanh::lean_dec_ref(v_res_579_);
    return v_res_581_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_recombineGoal(
    mut v_res_582_: *mut leanh::LeanObject,
    mut v_goal_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_focusHyp_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_596_: u8 = 0;
    let mut v_unused_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_584_ = leanh::lean_ctor_get(v_goal_583_, 0);
                v_00_u03c3s_585_ = leanh::lean_ctor_get(v_goal_583_, 1);
                v_target_586_ = leanh::lean_ctor_get(v_goal_583_, 3);
                v_isSharedCheck_596_ = (!leanh::lean_is_exclusive(v_goal_583_)) as u8;
                if v_isSharedCheck_596_ == 0 {
                    v_unused_597_ = leanh::lean_ctor_get(v_goal_583_, 2);
                    leanh::lean_dec(v_unused_597_);
                    v___x_588_ = v_goal_583_;
                    v_isShared_589_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_target_586_);
                    leanh::lean_inc(v_00_u03c3s_585_);
                    leanh::lean_inc(v_u_584_);
                    leanh::lean_dec(v_goal_583_);
                    v___x_588_ = leanh::lean_box(0);
                    v_isShared_589_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_focusHyp_590_ = leanh::lean_ctor_get(v_res_582_, 0);
                leanh::lean_inc_ref(v_focusHyp_590_);
                v_restHyps_591_ = leanh::lean_ctor_get(v_res_582_, 1);
                leanh::lean_inc_ref(v_restHyps_591_);
                leanh::lean_dec_ref(v_res_582_);
                leanh::lean_inc_ref(v_00_u03c3s_585_);
                leanh::lean_inc(v_u_584_);
                v___x_592_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_584_,
                    v_00_u03c3s_585_,
                    v_restHyps_591_,
                    v_focusHyp_590_,
                );
                if v_isShared_589_ == 0 {
                    leanh::lean_ctor_set(v___x_588_, 2, v___x_592_);
                    v___x_594_ = v___x_588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_595_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_595_, 0, v_u_584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_595_, 1, v_00_u03c3s_585_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_595_, 2, v___x_592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_595_, 3, v_target_586_);
                    v___x_594_ = v_reuseFailAlloc_595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_594_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps(
    mut v_res_606_: *mut leanh::LeanObject,
    mut v_goal_607_: *mut leanh::LeanObject,
    mut v_e_u2082_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_u_609_ = leanh::lean_ctor_get(v_goal_607_, 0);
    leanh::lean_inc_n(v_u_609_, 2);
    v_00_u03c3s_610_ = leanh::lean_ctor_get(v_goal_607_, 1);
    leanh::lean_inc_ref_n(v_00_u03c3s_610_, 2);
    v_hyps_611_ = leanh::lean_ctor_get(v_goal_607_, 2);
    leanh::lean_inc_ref(v_hyps_611_);
    v_target_612_ = leanh::lean_ctor_get(v_goal_607_, 3);
    leanh::lean_inc_ref(v_target_612_);
    leanh::lean_dec_ref(v_goal_607_);
    v_focusHyp_613_ = leanh::lean_ctor_get(v_res_606_, 0);
    leanh::lean_inc_ref(v_focusHyp_613_);
    v_restHyps_614_ = leanh::lean_ctor_get(v_res_606_, 1);
    leanh::lean_inc_ref(v_restHyps_614_);
    v_proof_615_ = leanh::lean_ctor_get(v_res_606_, 2);
    leanh::lean_inc_ref(v_proof_615_);
    leanh::lean_dec_ref(v_res_606_);
    v___x_616_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1;
    v___x_617_ = leanh::lean_box(0);
    v___x_618_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_618_, 0, v_u_609_);
    leanh::lean_ctor_set(v___x_618_, 1, v___x_617_);
    v___x_619_ = l_Lean_mkConst(v___x_616_, v___x_618_);
    v___x_620_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
        v_u_609_,
        v_00_u03c3s_610_,
        v_restHyps_614_,
        v_focusHyp_613_,
    );
    v___x_621_ = l_Lean_mkApp6(
        v___x_619_,
        v_00_u03c3s_610_,
        v_hyps_611_,
        v___x_620_,
        v_target_612_,
        v_proof_615_,
        v_e_u2082_608_,
    );
    return v___x_621_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(
    mut v_msgData_622_: *mut leanh::LeanObject,
    mut v___y_623_: *mut leanh::LeanObject,
    mut v___y_624_: *mut leanh::LeanObject,
    mut v___y_625_: *mut leanh::LeanObject,
    mut v___y_626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = lean_st_ref_get(v___y_626_);
    v_env_629_ = leanh::lean_ctor_get(v___x_628_, 0);
    leanh::lean_inc_ref(v_env_629_);
    leanh::lean_dec(v___x_628_);
    v___x_630_ = lean_st_ref_get(v___y_624_);
    v_mctx_631_ = leanh::lean_ctor_get(v___x_630_, 0);
    leanh::lean_inc_ref(v_mctx_631_);
    leanh::lean_dec(v___x_630_);
    v_lctx_632_ = leanh::lean_ctor_get(v___y_623_, 2);
    v_options_633_ = leanh::lean_ctor_get(v___y_625_, 2);
    leanh::lean_inc_ref(v_options_633_);
    leanh::lean_inc_ref(v_lctx_632_);
    v___x_634_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_634_, 0, v_env_629_);
    leanh::lean_ctor_set(v___x_634_, 1, v_mctx_631_);
    leanh::lean_ctor_set(v___x_634_, 2, v_lctx_632_);
    leanh::lean_ctor_set(v___x_634_, 3, v_options_633_);
    v___x_635_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_635_, 0, v___x_634_);
    leanh::lean_ctor_set(v___x_635_, 1, v_msgData_622_);
    v___x_636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_636_, 0, v___x_635_);
    return v___x_636_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0___boxed(
    mut v_msgData_637_: *mut leanh::LeanObject,
    mut v___y_638_: *mut leanh::LeanObject,
    mut v___y_639_: *mut leanh::LeanObject,
    mut v___y_640_: *mut leanh::LeanObject,
    mut v___y_641_: *mut leanh::LeanObject,
    mut v___y_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(v_msgData_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
    leanh::lean_dec(v___y_641_);
    leanh::lean_dec_ref(v___y_640_);
    leanh::lean_dec(v___y_639_);
    leanh::lean_dec_ref(v___y_638_);
    return v_res_643_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(
    mut v_msg_644_: *mut leanh::LeanObject,
    mut v___y_645_: *mut leanh::LeanObject,
    mut v___y_646_: *mut leanh::LeanObject,
    mut v___y_647_: *mut leanh::LeanObject,
    mut v___y_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_650_ = leanh::lean_ctor_get(v___y_647_, 5);
                v___x_651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
                v_a_652_ = leanh::lean_ctor_get(v___x_651_, 0);
                v_isSharedCheck_660_ = (!leanh::lean_is_exclusive(v___x_651_)) as u8;
                if v_isSharedCheck_660_ == 0 {
                    v___x_654_ = v___x_651_;
                    v_isShared_655_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_652_);
                    leanh::lean_dec(v___x_651_);
                    v___x_654_ = leanh::lean_box(0);
                    v_isShared_655_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_650_);
                v___x_656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_656_, 0, v_ref_650_);
                leanh::lean_ctor_set(v___x_656_, 1, v_a_652_);
                if v_isShared_655_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_654_, 1);
                    leanh::lean_ctor_set(v___x_654_, 0, v___x_656_);
                    v___x_658_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
                    v___x_658_ = v_reuseFailAlloc_659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg___boxed(
    mut v_msg_661_: *mut leanh::LeanObject,
    mut v___y_662_: *mut leanh::LeanObject,
    mut v___y_663_: *mut leanh::LeanObject,
    mut v___y_664_: *mut leanh::LeanObject,
    mut v___y_665_: *mut leanh::LeanObject,
    mut v___y_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_667_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
    leanh::lean_dec(v___y_665_);
    leanh::lean_dec_ref(v___y_664_);
    leanh::lean_dec(v___y_663_);
    leanh::lean_dec_ref(v___y_662_);
    return v_res_667_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_669_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0;
    v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
    return v___x_670_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2;
    v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
    return v___x_673_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4;
    v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
    mut v_goal_677_: *mut leanh::LeanObject,
    mut v_name_678_: *mut leanh::LeanObject,
    mut v_a_679_: *mut leanh::LeanObject,
    mut v_a_680_: *mut leanh::LeanObject,
    mut v_a_681_: *mut leanh::LeanObject,
    mut v_a_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_695_: u8 = 0;
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut v_unused_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_684_ = l_Lean_TSyntax_getId(v_name_678_);
                leanh::lean_inc_ref(v_goal_677_);
                v___x_685_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_goal_677_, v___x_684_);
                leanh::lean_dec(v___x_684_);
                if leanh::lean_obj_tag(v___x_685_) == 1 {
                    v_val_686_ = leanh::lean_ctor_get(v___x_685_, 0);
                    leanh::lean_inc(v_val_686_);
                    leanh::lean_dec_ref_known(v___x_685_, 1);
                    v_focusHyp_687_ = leanh::lean_ctor_get(v_val_686_, 0);
                    leanh::lean_inc_ref(v_focusHyp_687_);
                    v___x_688_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_687_);
                    if leanh::lean_obj_tag(v___x_688_) == 1 {
                        v_val_689_ = leanh::lean_ctor_get(v___x_688_, 0);
                        leanh::lean_inc(v_val_689_);
                        leanh::lean_dec_ref_known(v___x_688_, 1);
                        v_00_u03c3s_690_ = leanh::lean_ctor_get(v_goal_677_, 1);
                        leanh::lean_inc_ref(v_00_u03c3s_690_);
                        leanh::lean_dec_ref(v_goal_677_);
                        v___x_691_ = 0;
                        v___x_692_ = l_Lean_Elab_Tactic_Do_ProofMode_addHypInfo(
                            v_name_678_,
                            v_00_u03c3s_690_,
                            v_val_689_,
                            v___x_691_,
                            v_a_679_,
                            v_a_680_,
                            v_a_681_,
                            v_a_682_,
                        );
                        if leanh::lean_obj_tag(v___x_692_) == 0 {
                            v_isSharedCheck_699_ =
                                (!leanh::lean_is_exclusive(v___x_692_)) as u8;
                            if v_isSharedCheck_699_ == 0 {
                                v_unused_700_ = leanh::lean_ctor_get(v___x_692_, 0);
                                leanh::lean_dec(v_unused_700_);
                                v___x_694_ = v___x_692_;
                                v_isShared_695_ = v_isSharedCheck_699_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_692_);
                                v___x_694_ = leanh::lean_box(0);
                                v_isShared_695_ = v_isSharedCheck_699_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_686_);
                            v_a_701_ = leanh::lean_ctor_get(v___x_692_, 0);
                            v_isSharedCheck_708_ =
                                (!leanh::lean_is_exclusive(v___x_692_)) as u8;
                            if v_isSharedCheck_708_ == 0 {
                                v___x_703_ = v___x_692_;
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_701_);
                                leanh::lean_dec(v___x_692_);
                                v___x_703_ = leanh::lean_box(0);
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_688_);
                        leanh::lean_dec(v_val_686_);
                        leanh::lean_dec(v_name_678_);
                        leanh::lean_dec_ref(v_goal_677_);
                        v___x_709_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1);
                        v___x_710_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v___x_709_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
                        return v___x_710_;
                    }
                } else {
                    leanh::lean_dec(v___x_685_);
                    leanh::lean_dec_ref(v_goal_677_);
                    v___x_711_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3,
                    );
                    v___x_712_ = l_Lean_MessageData_ofSyntax(v_name_678_);
                    v___x_713_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_713_, 0, v___x_711_);
                    leanh::lean_ctor_set(v___x_713_, 1, v___x_712_);
                    v___x_714_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5,
                    );
                    v___x_715_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_715_, 0, v___x_713_);
                    leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
                    v___x_716_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v___x_715_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
                    return v___x_716_;
                }
            }
            1 => {
                if v_isShared_695_ == 0 {
                    leanh::lean_ctor_set(v___x_694_, 0, v_val_686_);
                    v___x_697_ = v___x_694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_698_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_698_, 0, v_val_686_);
                    v___x_697_ = v_reuseFailAlloc_698_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_697_;
            }
            3 => {
                if v_isShared_704_ == 0 {
                    v___x_706_ = v___x_703_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
                    v___x_706_ = v_reuseFailAlloc_707_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___boxed(
    mut v_goal_717_: *mut leanh::LeanObject,
    mut v_name_718_: *mut leanh::LeanObject,
    mut v_a_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_a_721_: *mut leanh::LeanObject,
    mut v_a_722_: *mut leanh::LeanObject,
    mut v_a_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
        v_goal_717_,
        v_name_718_,
        v_a_719_,
        v_a_720_,
        v_a_721_,
        v_a_722_,
    );
    leanh::lean_dec(v_a_722_);
    leanh::lean_dec_ref(v_a_721_);
    leanh::lean_dec(v_a_720_);
    leanh::lean_dec_ref(v_a_719_);
    return v_res_724_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0(
    mut v_00_u03b1_725_: *mut leanh::LeanObject,
    mut v_msg_726_: *mut leanh::LeanObject,
    mut v___y_727_: *mut leanh::LeanObject,
    mut v___y_728_: *mut leanh::LeanObject,
    mut v___y_729_: *mut leanh::LeanObject,
    mut v___y_730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
    return v___x_732_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___boxed(
    mut v_00_u03b1_733_: *mut leanh::LeanObject,
    mut v_msg_734_: *mut leanh::LeanObject,
    mut v___y_735_: *mut leanh::LeanObject,
    mut v___y_736_: *mut leanh::LeanObject,
    mut v___y_737_: *mut leanh::LeanObject,
    mut v___y_738_: *mut leanh::LeanObject,
    mut v___y_739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_740_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0(
            v_00_u03b1_733_,
            v_msg_734_,
            v___y_735_,
            v___y_736_,
            v___y_737_,
            v___y_738_,
        );
    leanh::lean_dec(v___y_738_);
    leanh::lean_dec_ref(v___y_737_);
    leanh::lean_dec(v___y_736_);
    leanh::lean_dec_ref(v___y_735_);
    return v_res_740_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default();
    leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default,
    );
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult();
    leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
}