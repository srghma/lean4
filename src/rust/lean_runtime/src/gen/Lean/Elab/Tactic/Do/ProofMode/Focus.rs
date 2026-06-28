// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Focus
// Imports: Lean.Elab.Tactic.Do.ProofMode.MGoal
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6};
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
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_name_eq, lean_panic_fn_borrowed};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_dbg_to_string;
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17542774118954891045 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value:
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut crate::leanh::LeanObject,
        280574599804500352 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__5_value)
            as *mut crate::leanh::LeanObject,
        17031249732047591641 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut crate::leanh::LeanObject,
        280574599804500352 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__7_value)
            as *mut crate::leanh::LeanObject,
        15785676217249922417 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_3:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_4:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_3)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut crate::leanh::LeanObject,
        280574599804500352 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value_aux_4)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__9_value)
            as *mut crate::leanh::LeanObject,
        2568375699356494615 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13_value:
    crate::leanh::LeanStringObject<47> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8550510443043304393 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__1_value)
            as *mut crate::leanh::LeanObject,
        14477891125163417350 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15734321041234825264 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7300584325018775040 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13332341187416043682 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18104247681175793831 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_4:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_3
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__4_value)
            as *mut crate::leanh::LeanObject,
        280574599804500352 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value_aux_4
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        14389574595038836286 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 104, 121, 112, 111, 116, 104, 101, 115, 105, 115,
        32, 96, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = crate::leanh::lean_box(0);
    v___x_375_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__1;
    v___x_376_ = l_Lean_Expr_const___override(v___x_375_, v___x_374_);
    return v___x_376_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default___closed__2,
    );
    v___x_378_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_378_, 0, v___x_377_);
    crate::leanh::lean_ctor_set(v___x_378_, 1, v___x_377_);
    crate::leanh::lean_ctor_set(v___x_378_, 2, v___x_377_);
    return v___x_378_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = crate::leanh::lean_obj_once(
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default;
    return v___x_380_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Tactic_Do_ProofMode_focusHyp_spec__0(
    mut v_msg_381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_382_ = crate::leanh::lean_box(0);
    v___x_383_ = lean_panic_fn_borrowed(v___x_382_, v_msg_381_);
    return v___x_383_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
    mut v_u_416_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_417_: *mut crate::leanh::LeanObject,
    mut v_e_418_: *mut crate::leanh::LeanObject,
    mut v_name_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_424_: u8 = 0;
    let mut v_name_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_428_: u8 = 0;
    let mut v___x_429_: u8 = 0;
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_443_: u8 = 0;
    let mut v_unused_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_446_: u8 = 0;
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_460_: u8 = 0;
    let mut v_focusHyp_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_466_: u8 = 0;
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut v_val_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v_focusHyp_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_518_: u8 = 0;
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut v_isSharedCheck_520_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_418_);
                v___x_420_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_e_418_);
                if crate::leanh::lean_obj_tag(v___x_420_) == 1 {
                    v_val_421_ = crate::leanh::lean_ctor_get(v___x_420_, 0);
                    v_isSharedCheck_446_ = (!crate::leanh::lean_is_exclusive(v___x_420_)) as u8;
                    if v_isSharedCheck_446_ == 0 {
                        v___x_423_ = v___x_420_;
                        v_isShared_424_ = v_isSharedCheck_446_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_421_);
                        crate::leanh::lean_dec(v___x_420_);
                        v___x_423_ = crate::leanh::lean_box(0);
                        v_isShared_424_ = v_isSharedCheck_446_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_420_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_417_);
                    crate::leanh::lean_dec(v_u_416_);
                    v___x_447_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_e_418_);
                    if crate::leanh::lean_obj_tag(v___x_447_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_418_);
                        v_val_448_ = crate::leanh::lean_ctor_get(v___x_447_, 0);
                        crate::leanh::lean_inc(v_val_448_);
                        crate::leanh::lean_dec_ref_known(v___x_447_, 1);
                        v_snd_449_ = crate::leanh::lean_ctor_get(v_val_448_, 1);
                        crate::leanh::lean_inc(v_snd_449_);
                        v_snd_450_ = crate::leanh::lean_ctor_get(v_snd_449_, 1);
                        crate::leanh::lean_inc(v_snd_450_);
                        v_fst_451_ = crate::leanh::lean_ctor_get(v_val_448_, 0);
                        crate::leanh::lean_inc_n(v_fst_451_, 2);
                        crate::leanh::lean_dec(v_val_448_);
                        v_fst_452_ = crate::leanh::lean_ctor_get(v_snd_449_, 0);
                        crate::leanh::lean_inc_n(v_fst_452_, 2);
                        crate::leanh::lean_dec(v_snd_449_);
                        v_fst_453_ = crate::leanh::lean_ctor_get(v_snd_450_, 0);
                        crate::leanh::lean_inc(v_fst_453_);
                        v_snd_454_ = crate::leanh::lean_ctor_get(v_snd_450_, 1);
                        crate::leanh::lean_inc_n(v_snd_454_, 2);
                        crate::leanh::lean_dec(v_snd_450_);
                        v___x_455_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
                            v_fst_451_,
                            v_fst_452_,
                            v_snd_454_,
                            v_name_419_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_455_) == 0 {
                            crate::leanh::lean_inc(v_fst_453_);
                            crate::leanh::lean_inc(v_fst_452_);
                            crate::leanh::lean_inc(v_fst_451_);
                            v___x_456_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
                                v_fst_451_,
                                v_fst_452_,
                                v_fst_453_,
                                v_name_419_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_456_) == 0 {
                                crate::leanh::lean_dec(v_snd_454_);
                                crate::leanh::lean_dec(v_fst_453_);
                                crate::leanh::lean_dec(v_fst_452_);
                                crate::leanh::lean_dec(v_fst_451_);
                                return v___x_456_;
                            } else {
                                v_val_457_ = crate::leanh::lean_ctor_get(v___x_456_, 0);
                                v_isSharedCheck_488_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_456_)) as u8;
                                if v_isSharedCheck_488_ == 0 {
                                    v___x_459_ = v___x_456_;
                                    v_isShared_460_ = v_isSharedCheck_488_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_457_);
                                    crate::leanh::lean_dec(v___x_456_);
                                    v___x_459_ = crate::leanh::lean_box(0);
                                    v_isShared_460_ = v_isSharedCheck_488_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_val_489_ = crate::leanh::lean_ctor_get(v___x_455_, 0);
                            v_isSharedCheck_520_ =
                                (!crate::leanh::lean_is_exclusive(v___x_455_)) as u8;
                            if v_isSharedCheck_520_ == 0 {
                                v___x_491_ = v___x_455_;
                                v_isShared_492_ = v_isSharedCheck_520_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_489_);
                                crate::leanh::lean_dec(v___x_455_);
                                v___x_491_ = crate::leanh::lean_box(0);
                                v_isShared_492_ = v_isSharedCheck_520_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_447_);
                        crate::leanh::lean_inc_ref(v_e_418_);
                        v___x_521_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_e_418_);
                        if crate::leanh::lean_obj_tag(v___x_521_) == 1 {
                            crate::leanh::lean_dec_ref_known(v___x_521_, 1);
                            crate::leanh::lean_dec_ref(v_e_418_);
                            v___x_522_ = crate::leanh::lean_box(0);
                            return v___x_522_;
                        } else {
                            crate::leanh::lean_dec(v___x_521_);
                            v___x_523_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__11;
                            v___x_524_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__12;
                            v___x_525_ = crate::leanh::lean_unsigned_to_nat(46);
                            v___x_526_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_527_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__13;
                            v___x_528_ = lean_expr_dbg_to_string(v_e_418_);
                            crate::leanh::lean_dec_ref(v_e_418_);
                            v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
                            crate::leanh::lean_dec_ref(v___x_528_);
                            v___x_530_ = l_mkPanicMessageWithDecl(
                                v___x_523_, v___x_524_, v___x_525_, v___x_526_, v___x_529_,
                            );
                            crate::leanh::lean_dec_ref(v___x_529_);
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
                v_name_425_ = crate::leanh::lean_ctor_get(v_val_421_, 0);
                v_isSharedCheck_443_ = (!crate::leanh::lean_is_exclusive(v_val_421_)) as u8;
                if v_isSharedCheck_443_ == 0 {
                    v_unused_444_ = crate::leanh::lean_ctor_get(v_val_421_, 2);
                    crate::leanh::lean_dec(v_unused_444_);
                    v_unused_445_ = crate::leanh::lean_ctor_get(v_val_421_, 1);
                    crate::leanh::lean_dec(v_unused_445_);
                    v___x_427_ = v_val_421_;
                    v_isShared_428_ = v_isSharedCheck_443_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_425_);
                    crate::leanh::lean_dec(v_val_421_);
                    v___x_427_ = crate::leanh::lean_box(0);
                    v_isShared_428_ = v_isSharedCheck_443_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_429_ = lean_name_eq(v_name_425_, v_name_419_);
                crate::leanh::lean_dec(v_name_425_);
                if v___x_429_ == 0 {
                    crate::leanh::lean_del_object(v___x_427_);
                    crate::leanh::lean_del_object(v___x_423_);
                    crate::leanh::lean_dec_ref(v_e_418_);
                    crate::leanh::lean_dec_ref(v_00_u03c3s_417_);
                    crate::leanh::lean_dec(v_u_416_);
                    v___x_430_ = crate::leanh::lean_box(0);
                    return v___x_430_;
                } else {
                    crate::leanh::lean_inc_ref(v_00_u03c3s_417_);
                    crate::leanh::lean_inc(v_u_416_);
                    v___x_431_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_u_416_, v_00_u03c3s_417_);
                    v___x_432_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__6;
                    v___x_433_ = crate::leanh::lean_box(0);
                    v___x_434_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_434_, 0, v_u_416_);
                    crate::leanh::lean_ctor_set(v___x_434_, 1, v___x_433_);
                    v___x_435_ = l_Lean_mkConst(v___x_432_, v___x_434_);
                    crate::leanh::lean_inc_ref(v_e_418_);
                    v___x_436_ = l_Lean_mkAppB(v___x_435_, v_00_u03c3s_417_, v_e_418_);
                    if v_isShared_428_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_427_, 2, v___x_436_);
                        crate::leanh::lean_ctor_set(v___x_427_, 1, v___x_431_);
                        crate::leanh::lean_ctor_set(v___x_427_, 0, v_e_418_);
                        v___x_438_ = v___x_427_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_442_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_442_, 0, v_e_418_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_431_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_442_, 2, v___x_436_);
                        v___x_438_ = v_reuseFailAlloc_442_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_424_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_423_, 0, v___x_438_);
                    v___x_440_ = v___x_423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
                    v___x_440_ = v_reuseFailAlloc_441_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_440_;
            }
            5 => {
                v_focusHyp_461_ = crate::leanh::lean_ctor_get(v_val_457_, 0);
                v_restHyps_462_ = crate::leanh::lean_ctor_get(v_val_457_, 1);
                v_proof_463_ = crate::leanh::lean_ctor_get(v_val_457_, 2);
                v_isSharedCheck_487_ = (!crate::leanh::lean_is_exclusive(v_val_457_)) as u8;
                if v_isSharedCheck_487_ == 0 {
                    v___x_465_ = v_val_457_;
                    v_isShared_466_ = v_isSharedCheck_487_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_463_);
                    crate::leanh::lean_inc(v_restHyps_462_);
                    crate::leanh::lean_inc(v_focusHyp_461_);
                    crate::leanh::lean_dec(v_val_457_);
                    v___x_465_ = crate::leanh::lean_box(0);
                    v_isShared_466_ = v_isSharedCheck_487_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc(v_snd_454_);
                crate::leanh::lean_inc_ref(v_restHyps_462_);
                crate::leanh::lean_inc(v_fst_452_);
                crate::leanh::lean_inc(v_fst_451_);
                v___x_467_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_fst_451_,
                    v_fst_452_,
                    v_restHyps_462_,
                    v_snd_454_,
                );
                v_fst_468_ = crate::leanh::lean_ctor_get(v___x_467_, 0);
                v_snd_469_ = crate::leanh::lean_ctor_get(v___x_467_, 1);
                v_isSharedCheck_486_ = (!crate::leanh::lean_is_exclusive(v___x_467_)) as u8;
                if v_isSharedCheck_486_ == 0 {
                    v___x_471_ = v___x_467_;
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_469_);
                    crate::leanh::lean_inc(v_fst_468_);
                    crate::leanh::lean_dec(v___x_467_);
                    v___x_471_ = crate::leanh::lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_473_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__8;
                v___x_474_ = crate::leanh::lean_box(0);
                if v_isShared_472_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_471_, 1);
                    crate::leanh::lean_ctor_set(v___x_471_, 1, v___x_474_);
                    crate::leanh::lean_ctor_set(v___x_471_, 0, v_fst_451_);
                    v___x_476_ = v___x_471_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_485_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 0, v_fst_451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_474_);
                    v___x_476_ = v_reuseFailAlloc_485_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_477_ = l_Lean_mkConst(v___x_473_, v___x_476_);
                crate::leanh::lean_inc_ref(v_focusHyp_461_);
                crate::leanh::lean_inc(v_fst_468_);
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
                    crate::leanh::lean_ctor_set(v___x_465_, 2, v___x_478_);
                    crate::leanh::lean_ctor_set(v___x_465_, 1, v_fst_468_);
                    v___x_480_ = v___x_465_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_484_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_484_, 0, v_focusHyp_461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_484_, 1, v_fst_468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_484_, 2, v___x_478_);
                    v___x_480_ = v_reuseFailAlloc_484_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_459_, 0, v___x_480_);
                    v___x_482_ = v___x_459_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
                    v___x_482_ = v_reuseFailAlloc_483_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_482_;
            }
            11 => {
                v_focusHyp_493_ = crate::leanh::lean_ctor_get(v_val_489_, 0);
                v_restHyps_494_ = crate::leanh::lean_ctor_get(v_val_489_, 1);
                v_proof_495_ = crate::leanh::lean_ctor_get(v_val_489_, 2);
                v_isSharedCheck_519_ = (!crate::leanh::lean_is_exclusive(v_val_489_)) as u8;
                if v_isSharedCheck_519_ == 0 {
                    v___x_497_ = v_val_489_;
                    v_isShared_498_ = v_isSharedCheck_519_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_proof_495_);
                    crate::leanh::lean_inc(v_restHyps_494_);
                    crate::leanh::lean_inc(v_focusHyp_493_);
                    crate::leanh::lean_dec(v_val_489_);
                    v___x_497_ = crate::leanh::lean_box(0);
                    v_isShared_498_ = v_isSharedCheck_519_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_ref(v_restHyps_494_);
                crate::leanh::lean_inc(v_fst_453_);
                crate::leanh::lean_inc(v_fst_452_);
                crate::leanh::lean_inc(v_fst_451_);
                v___x_499_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd(
                    v_fst_451_,
                    v_fst_452_,
                    v_fst_453_,
                    v_restHyps_494_,
                );
                v_fst_500_ = crate::leanh::lean_ctor_get(v___x_499_, 0);
                v_snd_501_ = crate::leanh::lean_ctor_get(v___x_499_, 1);
                v_isSharedCheck_518_ = (!crate::leanh::lean_is_exclusive(v___x_499_)) as u8;
                if v_isSharedCheck_518_ == 0 {
                    v___x_503_ = v___x_499_;
                    v_isShared_504_ = v_isSharedCheck_518_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_501_);
                    crate::leanh::lean_inc(v_fst_500_);
                    crate::leanh::lean_dec(v___x_499_);
                    v___x_503_ = crate::leanh::lean_box(0);
                    v_isShared_504_ = v_isSharedCheck_518_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_505_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp___closed__10;
                v___x_506_ = crate::leanh::lean_box(0);
                if v_isShared_504_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_503_, 1);
                    crate::leanh::lean_ctor_set(v___x_503_, 1, v___x_506_);
                    crate::leanh::lean_ctor_set(v___x_503_, 0, v_fst_451_);
                    v___x_508_ = v___x_503_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_517_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_517_, 0, v_fst_451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_517_, 1, v___x_506_);
                    v___x_508_ = v_reuseFailAlloc_517_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_509_ = l_Lean_mkConst(v___x_505_, v___x_508_);
                crate::leanh::lean_inc_ref(v_focusHyp_493_);
                crate::leanh::lean_inc(v_fst_500_);
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
                    crate::leanh::lean_ctor_set(v___x_497_, 2, v___x_510_);
                    crate::leanh::lean_ctor_set(v___x_497_, 1, v_fst_500_);
                    v___x_512_ = v___x_497_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_516_, 0, v_focusHyp_493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_516_, 1, v_fst_500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_516_, 2, v___x_510_);
                    v___x_512_ = v_reuseFailAlloc_516_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_491_, 0, v___x_512_);
                    v___x_514_ = v___x_491_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_515_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
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
    mut v_u_532_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_533_: *mut crate::leanh::LeanObject,
    mut v_e_534_: *mut crate::leanh::LeanObject,
    mut v_name_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_536_ =
        l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(v_u_532_, v_00_u03c3s_533_, v_e_534_, v_name_535_);
    crate::leanh::lean_dec(v_name_535_);
    return v_res_536_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(
    mut v_goal_537_: *mut crate::leanh::LeanObject,
    mut v_name_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_u_539_ = crate::leanh::lean_ctor_get(v_goal_537_, 0);
    crate::leanh::lean_inc(v_u_539_);
    v_00_u03c3s_540_ = crate::leanh::lean_ctor_get(v_goal_537_, 1);
    crate::leanh::lean_inc_ref(v_00_u03c3s_540_);
    v_hyps_541_ = crate::leanh::lean_ctor_get(v_goal_537_, 2);
    crate::leanh::lean_inc_ref(v_hyps_541_);
    crate::leanh::lean_dec_ref(v_goal_537_);
    v___x_542_ = l_Lean_Elab_Tactic_Do_ProofMode_focusHyp(
        v_u_539_,
        v_00_u03c3s_540_,
        v_hyps_541_,
        v_name_538_,
    );
    return v___x_542_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp___boxed(
    mut v_goal_543_: *mut crate::leanh::LeanObject,
    mut v_name_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_goal_543_, v_name_544_);
    crate::leanh::lean_dec(v_name_544_);
    return v_res_545_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl(
    mut v_u_554_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3s_555_: *mut crate::leanh::LeanObject,
    mut v_restHyps_556_: *mut crate::leanh::LeanObject,
    mut v_focusHyp_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_558_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_refl___closed__2;
    v___x_559_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_u_554_);
    v___x_560_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_560_, 0, v_u_554_);
    crate::leanh::lean_ctor_set(v___x_560_, 1, v___x_559_);
    v___x_561_ = l_Lean_mkConst(v___x_558_, v___x_560_);
    crate::leanh::lean_inc_ref(v_focusHyp_557_);
    crate::leanh::lean_inc_ref(v_restHyps_556_);
    crate::leanh::lean_inc_ref(v_00_u03c3s_555_);
    v___x_562_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
        v_u_554_,
        v_00_u03c3s_555_,
        v_restHyps_556_,
        v_focusHyp_557_,
    );
    v_proof_563_ = l_Lean_mkAppB(v___x_561_, v_00_u03c3s_555_, v___x_562_);
    v___x_564_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_564_, 0, v_focusHyp_557_);
    crate::leanh::lean_ctor_set(v___x_564_, 1, v_restHyps_556_);
    crate::leanh::lean_ctor_set(v___x_564_, 2, v_proof_563_);
    return v___x_564_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(
    mut v_res_565_: *mut crate::leanh::LeanObject,
    mut v_goal_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v_restHyps_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut v_unused_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_567_ = crate::leanh::lean_ctor_get(v_goal_566_, 0);
                v_00_u03c3s_568_ = crate::leanh::lean_ctor_get(v_goal_566_, 1);
                v_target_569_ = crate::leanh::lean_ctor_get(v_goal_566_, 3);
                v_isSharedCheck_577_ = (!crate::leanh::lean_is_exclusive(v_goal_566_)) as u8;
                if v_isSharedCheck_577_ == 0 {
                    v_unused_578_ = crate::leanh::lean_ctor_get(v_goal_566_, 2);
                    crate::leanh::lean_dec(v_unused_578_);
                    v___x_571_ = v_goal_566_;
                    v_isShared_572_ = v_isSharedCheck_577_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_569_);
                    crate::leanh::lean_inc(v_00_u03c3s_568_);
                    crate::leanh::lean_inc(v_u_567_);
                    crate::leanh::lean_dec(v_goal_566_);
                    v___x_571_ = crate::leanh::lean_box(0);
                    v_isShared_572_ = v_isSharedCheck_577_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_restHyps_573_ = crate::leanh::lean_ctor_get(v_res_565_, 1);
                crate::leanh::lean_inc_ref(v_restHyps_573_);
                if v_isShared_572_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_571_, 2, v_restHyps_573_);
                    v___x_575_ = v___x_571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_576_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_576_, 0, v_u_567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_576_, 1, v_00_u03c3s_568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_576_, 2, v_restHyps_573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_576_, 3, v_target_569_);
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
    mut v_res_579_: *mut crate::leanh::LeanObject,
    mut v_goal_580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_restGoal(v_res_579_, v_goal_580_);
    crate::leanh::lean_dec_ref(v_res_579_);
    return v_res_581_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_recombineGoal(
    mut v_res_582_: *mut crate::leanh::LeanObject,
    mut v_goal_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_focusHyp_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_596_: u8 = 0;
    let mut v_unused_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_584_ = crate::leanh::lean_ctor_get(v_goal_583_, 0);
                v_00_u03c3s_585_ = crate::leanh::lean_ctor_get(v_goal_583_, 1);
                v_target_586_ = crate::leanh::lean_ctor_get(v_goal_583_, 3);
                v_isSharedCheck_596_ = (!crate::leanh::lean_is_exclusive(v_goal_583_)) as u8;
                if v_isSharedCheck_596_ == 0 {
                    v_unused_597_ = crate::leanh::lean_ctor_get(v_goal_583_, 2);
                    crate::leanh::lean_dec(v_unused_597_);
                    v___x_588_ = v_goal_583_;
                    v_isShared_589_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_target_586_);
                    crate::leanh::lean_inc(v_00_u03c3s_585_);
                    crate::leanh::lean_inc(v_u_584_);
                    crate::leanh::lean_dec(v_goal_583_);
                    v___x_588_ = crate::leanh::lean_box(0);
                    v_isShared_589_ = v_isSharedCheck_596_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_focusHyp_590_ = crate::leanh::lean_ctor_get(v_res_582_, 0);
                crate::leanh::lean_inc_ref(v_focusHyp_590_);
                v_restHyps_591_ = crate::leanh::lean_ctor_get(v_res_582_, 1);
                crate::leanh::lean_inc_ref(v_restHyps_591_);
                crate::leanh::lean_dec_ref(v_res_582_);
                crate::leanh::lean_inc_ref(v_00_u03c3s_585_);
                crate::leanh::lean_inc(v_u_584_);
                v___x_592_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_u_584_,
                    v_00_u03c3s_585_,
                    v_restHyps_591_,
                    v_focusHyp_590_,
                );
                if v_isShared_589_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_588_, 2, v___x_592_);
                    v___x_594_ = v___x_588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_595_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 0, v_u_584_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 1, v_00_u03c3s_585_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 2, v___x_592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_595_, 3, v_target_586_);
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
    mut v_res_606_: *mut crate::leanh::LeanObject,
    mut v_goal_607_: *mut crate::leanh::LeanObject,
    mut v_e_u2082_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hyps_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restHyps_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_u_609_ = crate::leanh::lean_ctor_get(v_goal_607_, 0);
    crate::leanh::lean_inc_n(v_u_609_, 2);
    v_00_u03c3s_610_ = crate::leanh::lean_ctor_get(v_goal_607_, 1);
    crate::leanh::lean_inc_ref_n(v_00_u03c3s_610_, 2);
    v_hyps_611_ = crate::leanh::lean_ctor_get(v_goal_607_, 2);
    crate::leanh::lean_inc_ref(v_hyps_611_);
    v_target_612_ = crate::leanh::lean_ctor_get(v_goal_607_, 3);
    crate::leanh::lean_inc_ref(v_target_612_);
    crate::leanh::lean_dec_ref(v_goal_607_);
    v_focusHyp_613_ = crate::leanh::lean_ctor_get(v_res_606_, 0);
    crate::leanh::lean_inc_ref(v_focusHyp_613_);
    v_restHyps_614_ = crate::leanh::lean_ctor_get(v_res_606_, 1);
    crate::leanh::lean_inc_ref(v_restHyps_614_);
    v_proof_615_ = crate::leanh::lean_ctor_get(v_res_606_, 2);
    crate::leanh::lean_inc_ref(v_proof_615_);
    crate::leanh::lean_dec_ref(v_res_606_);
    v___x_616_ = l_Lean_Elab_Tactic_Do_ProofMode_FocusResult_rewriteHyps___closed__1;
    v___x_617_ = crate::leanh::lean_box(0);
    v___x_618_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_618_, 0, v_u_609_);
    crate::leanh::lean_ctor_set(v___x_618_, 1, v___x_617_);
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
    mut v_msgData_622_: *mut crate::leanh::LeanObject,
    mut v___y_623_: *mut crate::leanh::LeanObject,
    mut v___y_624_: *mut crate::leanh::LeanObject,
    mut v___y_625_: *mut crate::leanh::LeanObject,
    mut v___y_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = lean_st_ref_get(v___y_626_);
    v_env_629_ = crate::leanh::lean_ctor_get(v___x_628_, 0);
    crate::leanh::lean_inc_ref(v_env_629_);
    crate::leanh::lean_dec(v___x_628_);
    v___x_630_ = lean_st_ref_get(v___y_624_);
    v_mctx_631_ = crate::leanh::lean_ctor_get(v___x_630_, 0);
    crate::leanh::lean_inc_ref(v_mctx_631_);
    crate::leanh::lean_dec(v___x_630_);
    v_lctx_632_ = crate::leanh::lean_ctor_get(v___y_623_, 2);
    v_options_633_ = crate::leanh::lean_ctor_get(v___y_625_, 2);
    crate::leanh::lean_inc_ref(v_options_633_);
    crate::leanh::lean_inc_ref(v_lctx_632_);
    v___x_634_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_634_, 0, v_env_629_);
    crate::leanh::lean_ctor_set(v___x_634_, 1, v_mctx_631_);
    crate::leanh::lean_ctor_set(v___x_634_, 2, v_lctx_632_);
    crate::leanh::lean_ctor_set(v___x_634_, 3, v_options_633_);
    v___x_635_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_635_, 0, v___x_634_);
    crate::leanh::lean_ctor_set(v___x_635_, 1, v_msgData_622_);
    v___x_636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_636_, 0, v___x_635_);
    return v___x_636_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0___boxed(
    mut v_msgData_637_: *mut crate::leanh::LeanObject,
    mut v___y_638_: *mut crate::leanh::LeanObject,
    mut v___y_639_: *mut crate::leanh::LeanObject,
    mut v___y_640_: *mut crate::leanh::LeanObject,
    mut v___y_641_: *mut crate::leanh::LeanObject,
    mut v___y_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_643_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(v_msgData_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
    crate::leanh::lean_dec(v___y_641_);
    crate::leanh::lean_dec_ref(v___y_640_);
    crate::leanh::lean_dec(v___y_639_);
    crate::leanh::lean_dec_ref(v___y_638_);
    return v_res_643_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(
    mut v_msg_644_: *mut crate::leanh::LeanObject,
    mut v___y_645_: *mut crate::leanh::LeanObject,
    mut v___y_646_: *mut crate::leanh::LeanObject,
    mut v___y_647_: *mut crate::leanh::LeanObject,
    mut v___y_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_650_ = crate::leanh::lean_ctor_get(v___y_647_, 5);
                v___x_651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0_spec__0(v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
                v_a_652_ = crate::leanh::lean_ctor_get(v___x_651_, 0);
                v_isSharedCheck_660_ = (!crate::leanh::lean_is_exclusive(v___x_651_)) as u8;
                if v_isSharedCheck_660_ == 0 {
                    v___x_654_ = v___x_651_;
                    v_isShared_655_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_652_);
                    crate::leanh::lean_dec(v___x_651_);
                    v___x_654_ = crate::leanh::lean_box(0);
                    v_isShared_655_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_650_);
                v___x_656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_656_, 0, v_ref_650_);
                crate::leanh::lean_ctor_set(v___x_656_, 1, v_a_652_);
                if v_isShared_655_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_654_, 1);
                    crate::leanh::lean_ctor_set(v___x_654_, 0, v___x_656_);
                    v___x_658_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
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
    mut v_msg_661_: *mut crate::leanh::LeanObject,
    mut v___y_662_: *mut crate::leanh::LeanObject,
    mut v___y_663_: *mut crate::leanh::LeanObject,
    mut v___y_664_: *mut crate::leanh::LeanObject,
    mut v___y_665_: *mut crate::leanh::LeanObject,
    mut v___y_666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_667_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
    crate::leanh::lean_dec(v___y_665_);
    crate::leanh::lean_dec_ref(v___y_664_);
    crate::leanh::lean_dec(v___y_663_);
    crate::leanh::lean_dec_ref(v___y_662_);
    return v_res_667_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_669_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__0;
    v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
    return v___x_670_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__2;
    v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
    return v___x_673_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__4;
    v___x_676_ = l_Lean_stringToMessageData(v___x_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
    mut v_goal_677_: *mut crate::leanh::LeanObject,
    mut v_name_678_: *mut crate::leanh::LeanObject,
    mut v_a_679_: *mut crate::leanh::LeanObject,
    mut v_a_680_: *mut crate::leanh::LeanObject,
    mut v_a_681_: *mut crate::leanh::LeanObject,
    mut v_a_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_focusHyp_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_695_: u8 = 0;
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut v_unused_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_684_ = l_Lean_TSyntax_getId(v_name_678_);
                crate::leanh::lean_inc_ref(v_goal_677_);
                v___x_685_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHyp(v_goal_677_, v___x_684_);
                crate::leanh::lean_dec(v___x_684_);
                if crate::leanh::lean_obj_tag(v___x_685_) == 1 {
                    v_val_686_ = crate::leanh::lean_ctor_get(v___x_685_, 0);
                    crate::leanh::lean_inc(v_val_686_);
                    crate::leanh::lean_dec_ref_known(v___x_685_, 1);
                    v_focusHyp_687_ = crate::leanh::lean_ctor_get(v_val_686_, 0);
                    crate::leanh::lean_inc_ref(v_focusHyp_687_);
                    v___x_688_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_focusHyp_687_);
                    if crate::leanh::lean_obj_tag(v___x_688_) == 1 {
                        v_val_689_ = crate::leanh::lean_ctor_get(v___x_688_, 0);
                        crate::leanh::lean_inc(v_val_689_);
                        crate::leanh::lean_dec_ref_known(v___x_688_, 1);
                        v_00_u03c3s_690_ = crate::leanh::lean_ctor_get(v_goal_677_, 1);
                        crate::leanh::lean_inc_ref(v_00_u03c3s_690_);
                        crate::leanh::lean_dec_ref(v_goal_677_);
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
                        if crate::leanh::lean_obj_tag(v___x_692_) == 0 {
                            v_isSharedCheck_699_ =
                                (!crate::leanh::lean_is_exclusive(v___x_692_)) as u8;
                            if v_isSharedCheck_699_ == 0 {
                                v_unused_700_ = crate::leanh::lean_ctor_get(v___x_692_, 0);
                                crate::leanh::lean_dec(v_unused_700_);
                                v___x_694_ = v___x_692_;
                                v_isShared_695_ = v_isSharedCheck_699_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_692_);
                                v___x_694_ = crate::leanh::lean_box(0);
                                v_isShared_695_ = v_isSharedCheck_699_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_686_);
                            v_a_701_ = crate::leanh::lean_ctor_get(v___x_692_, 0);
                            v_isSharedCheck_708_ =
                                (!crate::leanh::lean_is_exclusive(v___x_692_)) as u8;
                            if v_isSharedCheck_708_ == 0 {
                                v___x_703_ = v___x_692_;
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_701_);
                                crate::leanh::lean_dec(v___x_692_);
                                v___x_703_ = crate::leanh::lean_box(0);
                                v_isShared_704_ = v_isSharedCheck_708_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_688_);
                        crate::leanh::lean_dec(v_val_686_);
                        crate::leanh::lean_dec(v_name_678_);
                        crate::leanh::lean_dec_ref(v_goal_677_);
                        v___x_709_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__1);
                        v___x_710_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v___x_709_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
                        return v___x_710_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_685_);
                    crate::leanh::lean_dec_ref(v_goal_677_);
                    v___x_711_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__3,
                    );
                    v___x_712_ = l_Lean_MessageData_ofSyntax(v_name_678_);
                    v___x_713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_713_, 0, v___x_711_);
                    crate::leanh::lean_ctor_set(v___x_713_, 1, v___x_712_);
                    v___x_714_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5_once
                        ),
                        _init_l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo___closed__5,
                    );
                    v___x_715_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_715_, 0, v___x_713_);
                    crate::leanh::lean_ctor_set(v___x_715_, 1, v___x_714_);
                    v___x_716_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v___x_715_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
                    return v___x_716_;
                }
            }
            1 => {
                if v_isShared_695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_694_, 0, v_val_686_);
                    v___x_697_ = v___x_694_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_698_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_698_, 0, v_val_686_);
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
                    v_reuseFailAlloc_707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
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
    mut v_goal_717_: *mut crate::leanh::LeanObject,
    mut v_name_718_: *mut crate::leanh::LeanObject,
    mut v_a_719_: *mut crate::leanh::LeanObject,
    mut v_a_720_: *mut crate::leanh::LeanObject,
    mut v_a_721_: *mut crate::leanh::LeanObject,
    mut v_a_722_: *mut crate::leanh::LeanObject,
    mut v_a_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo(
        v_goal_717_,
        v_name_718_,
        v_a_719_,
        v_a_720_,
        v_a_721_,
        v_a_722_,
    );
    crate::leanh::lean_dec(v_a_722_);
    crate::leanh::lean_dec_ref(v_a_721_);
    crate::leanh::lean_dec(v_a_720_);
    crate::leanh::lean_dec_ref(v_a_719_);
    return v_res_724_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0(
    mut v_00_u03b1_725_: *mut crate::leanh::LeanObject,
    mut v_msg_726_: *mut crate::leanh::LeanObject,
    mut v___y_727_: *mut crate::leanh::LeanObject,
    mut v___y_728_: *mut crate::leanh::LeanObject,
    mut v___y_729_: *mut crate::leanh::LeanObject,
    mut v___y_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___redArg(v_msg_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
    return v___x_732_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0___boxed(
    mut v_00_u03b1_733_: *mut crate::leanh::LeanObject,
    mut v_msg_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
    mut v___y_737_: *mut crate::leanh::LeanObject,
    mut v___y_738_: *mut crate::leanh::LeanObject,
    mut v___y_739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_740_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_MGoal_focusHypWithInfo_spec__0(
            v_00_u03b1_733_,
            v_msg_734_,
            v___y_735_,
            v___y_736_,
            v___y_737_,
            v___y_738_,
        );
    crate::leanh::lean_dec(v___y_738_);
    crate::leanh::lean_dec_ref(v___y_737_);
    crate::leanh::lean_dec(v___y_736_);
    crate::leanh::lean_dec_ref(v___y_735_);
    return v_res_740_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult_default,
    );
    l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult =
        _init_l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult();
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Tactic_Do_ProofMode_instInhabitedFocusResult);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
}
