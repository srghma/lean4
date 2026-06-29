// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Insts
// Imports: Lean.Meta.Tactic.Grind.Arith.EvalNum Lean.Meta.Tactic.Grind.SynthInstance Init.Grind.Ring
use crate::ffi::{lean_st_ref_get, lean_st_ref_set, lean_st_ref_take};
use crate::r#gen::Init::Grind::Ring::{
    initialize_Init_Grind_Ring, runtime_initialize_Init_Grind_Ring,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr3;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_hasMVar, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::EvalNum::{
    initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum, l_Lean_Meta_Grind_Arith_evalNat_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value:
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
    m_data: [71, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [73, 115, 67, 104, 97, 114, 80, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1:
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
            l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value:
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
            l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5319903737885873089 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value:
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
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [80, 111, 119, 73, 100, 101, 110, 116, 105, 116, 121, 0],
};
static mut l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value:
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
    m_data: [67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15814158821706329669 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value:
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
    m_data: [78, 97, 116, 77, 111, 100, 117, 108, 101, 0],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1:
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
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value:
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
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12969150934523051142 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        78, 111, 78, 97, 116, 90, 101, 114, 111, 68, 105, 118, 105, 115, 111, 114, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1:
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
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        13563742693681136756 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value:
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
            l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5648161575337860430 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(
    mut v_e_547_: *mut crate::leanh::LeanObject,
    mut v___y_548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_564_: u8 = 0;
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_unused_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_550_ = l_Lean_Expr_hasMVar(v_e_547_);
                if v___x_550_ == 0 {
                    v___x_551_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_551_, 0, v_e_547_);
                    return v___x_551_;
                } else {
                    v___x_552_ = lean_st_ref_get(v___y_548_);
                    v_mctx_553_ = crate::leanh::lean_ctor_get(v___x_552_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_553_);
                    crate::leanh::lean_dec(v___x_552_);
                    v___x_554_ = l_Lean_instantiateMVarsCore(v_mctx_553_, v_e_547_);
                    v_fst_555_ = crate::leanh::lean_ctor_get(v___x_554_, 0);
                    crate::leanh::lean_inc(v_fst_555_);
                    v_snd_556_ = crate::leanh::lean_ctor_get(v___x_554_, 1);
                    crate::leanh::lean_inc(v_snd_556_);
                    crate::leanh::lean_dec_ref(v___x_554_);
                    v___x_557_ = lean_st_ref_take(v___y_548_);
                    v_cache_558_ = crate::leanh::lean_ctor_get(v___x_557_, 1);
                    v_zetaDeltaFVarIds_559_ = crate::leanh::lean_ctor_get(v___x_557_, 2);
                    v_postponed_560_ = crate::leanh::lean_ctor_get(v___x_557_, 3);
                    v_diag_561_ = crate::leanh::lean_ctor_get(v___x_557_, 4);
                    v_isSharedCheck_570_ = (!crate::leanh::lean_is_exclusive(v___x_557_)) as u8;
                    if v_isSharedCheck_570_ == 0 {
                        v_unused_571_ = crate::leanh::lean_ctor_get(v___x_557_, 0);
                        crate::leanh::lean_dec(v_unused_571_);
                        v___x_563_ = v___x_557_;
                        v_isShared_564_ = v_isSharedCheck_570_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_561_);
                        crate::leanh::lean_inc(v_postponed_560_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_559_);
                        crate::leanh::lean_inc(v_cache_558_);
                        crate::leanh::lean_dec(v___x_557_);
                        v___x_563_ = crate::leanh::lean_box(0);
                        v_isShared_564_ = v_isSharedCheck_570_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_564_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_563_, 0, v_snd_556_);
                    v___x_566_ = v___x_563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_569_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 0, v_snd_556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 1, v_cache_558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 2, v_zetaDeltaFVarIds_559_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 3, v_postponed_560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_569_, 4, v_diag_561_);
                    v___x_566_ = v_reuseFailAlloc_569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_567_ = lean_st_ref_set(v___y_548_, v___x_566_);
                v___x_568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_568_, 0, v_fst_555_);
                return v___x_568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(
    mut v_e_572_: *mut crate::leanh::LeanObject,
    mut v___y_573_: *mut crate::leanh::LeanObject,
    mut v___y_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_575_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(
            v_e_572_, v___y_573_,
        );
    crate::leanh::lean_dec(v___y_573_);
    return v_res_575_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(
    mut v_e_576_: *mut crate::leanh::LeanObject,
    mut v___y_577_: *mut crate::leanh::LeanObject,
    mut v___y_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
    mut v___y_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
    mut v___y_582_: *mut crate::leanh::LeanObject,
    mut v___y_583_: *mut crate::leanh::LeanObject,
    mut v___y_584_: *mut crate::leanh::LeanObject,
    mut v___y_585_: *mut crate::leanh::LeanObject,
    mut v___y_586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_588_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(
            v_e_576_, v___y_584_,
        );
    return v___x_588_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___boxed(
    mut v_e_589_: *mut crate::leanh::LeanObject,
    mut v___y_590_: *mut crate::leanh::LeanObject,
    mut v___y_591_: *mut crate::leanh::LeanObject,
    mut v___y_592_: *mut crate::leanh::LeanObject,
    mut v___y_593_: *mut crate::leanh::LeanObject,
    mut v___y_594_: *mut crate::leanh::LeanObject,
    mut v___y_595_: *mut crate::leanh::LeanObject,
    mut v___y_596_: *mut crate::leanh::LeanObject,
    mut v___y_597_: *mut crate::leanh::LeanObject,
    mut v___y_598_: *mut crate::leanh::LeanObject,
    mut v___y_599_: *mut crate::leanh::LeanObject,
    mut v___y_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_601_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0(
        v_e_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_,
        v___y_596_, v___y_597_, v___y_598_, v___y_599_,
    );
    crate::leanh::lean_dec(v___y_599_);
    crate::leanh::lean_dec_ref(v___y_598_);
    crate::leanh::lean_dec(v___y_597_);
    crate::leanh::lean_dec_ref(v___y_596_);
    crate::leanh::lean_dec(v___y_595_);
    crate::leanh::lean_dec_ref(v___y_594_);
    crate::leanh::lean_dec(v___y_593_);
    crate::leanh::lean_dec_ref(v___y_592_);
    crate::leanh::lean_dec(v___y_591_);
    crate::leanh::lean_dec(v___y_590_);
    return v_res_601_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(
    mut v_k_602_: *mut crate::leanh::LeanObject,
    mut v___y_603_: *mut crate::leanh::LeanObject,
    mut v___y_604_: *mut crate::leanh::LeanObject,
    mut v___y_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
    mut v___y_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
    mut v___y_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_608_);
    crate::leanh::lean_inc_ref(v___y_607_);
    crate::leanh::lean_inc(v___y_606_);
    crate::leanh::lean_inc_ref(v___y_605_);
    crate::leanh::lean_inc(v___y_604_);
    crate::leanh::lean_inc(v___y_603_);
    v___x_614_ = crate::leanh::lean_apply_11(
        v_k_602_,
        v___y_603_,
        v___y_604_,
        v___y_605_,
        v___y_606_,
        v___y_607_,
        v___y_608_,
        v___y_609_,
        v___y_610_,
        v___y_611_,
        v___y_612_,
        crate::leanh::lean_box(0),
    );
    return v___x_614_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(
    mut v_k_615_: *mut crate::leanh::LeanObject,
    mut v___y_616_: *mut crate::leanh::LeanObject,
    mut v___y_617_: *mut crate::leanh::LeanObject,
    mut v___y_618_: *mut crate::leanh::LeanObject,
    mut v___y_619_: *mut crate::leanh::LeanObject,
    mut v___y_620_: *mut crate::leanh::LeanObject,
    mut v___y_621_: *mut crate::leanh::LeanObject,
    mut v___y_622_: *mut crate::leanh::LeanObject,
    mut v___y_623_: *mut crate::leanh::LeanObject,
    mut v___y_624_: *mut crate::leanh::LeanObject,
    mut v___y_625_: *mut crate::leanh::LeanObject,
    mut v___y_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_627_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
    crate::leanh::lean_dec(v___y_621_);
    crate::leanh::lean_dec_ref(v___y_620_);
    crate::leanh::lean_dec(v___y_619_);
    crate::leanh::lean_dec_ref(v___y_618_);
    crate::leanh::lean_dec(v___y_617_);
    crate::leanh::lean_dec(v___y_616_);
    return v_res_627_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(
    mut v_k_628_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_629_: u8,
    mut v___y_630_: *mut crate::leanh::LeanObject,
    mut v___y_631_: *mut crate::leanh::LeanObject,
    mut v___y_632_: *mut crate::leanh::LeanObject,
    mut v___y_633_: *mut crate::leanh::LeanObject,
    mut v___y_634_: *mut crate::leanh::LeanObject,
    mut v___y_635_: *mut crate::leanh::LeanObject,
    mut v___y_636_: *mut crate::leanh::LeanObject,
    mut v___y_637_: *mut crate::leanh::LeanObject,
    mut v___y_638_: *mut crate::leanh::LeanObject,
    mut v___y_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_646_: u8 = 0;
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_635_);
                crate::leanh::lean_inc_ref(v___y_634_);
                crate::leanh::lean_inc(v___y_633_);
                crate::leanh::lean_inc_ref(v___y_632_);
                crate::leanh::lean_inc(v___y_631_);
                crate::leanh::lean_inc(v___y_630_);
                v___f_641_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 7);
                crate::leanh::lean_closure_set(v___f_641_, 0, v_k_628_);
                crate::leanh::lean_closure_set(v___f_641_, 1, v___y_630_);
                crate::leanh::lean_closure_set(v___f_641_, 2, v___y_631_);
                crate::leanh::lean_closure_set(v___f_641_, 3, v___y_632_);
                crate::leanh::lean_closure_set(v___f_641_, 4, v___y_633_);
                crate::leanh::lean_closure_set(v___f_641_, 5, v___y_634_);
                crate::leanh::lean_closure_set(v___f_641_, 6, v___y_635_);
                v___x_642_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_629_,
                    v___f_641_,
                    v___y_636_,
                    v___y_637_,
                    v___y_638_,
                    v___y_639_,
                );
                if crate::leanh::lean_obj_tag(v___x_642_) == 0 {
                    return v___x_642_;
                } else {
                    v_a_643_ = crate::leanh::lean_ctor_get(v___x_642_, 0);
                    v_isSharedCheck_650_ = (!crate::leanh::lean_is_exclusive(v___x_642_)) as u8;
                    if v_isSharedCheck_650_ == 0 {
                        v___x_645_ = v___x_642_;
                        v_isShared_646_ = v_isSharedCheck_650_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_643_);
                        crate::leanh::lean_dec(v___x_642_);
                        v___x_645_ = crate::leanh::lean_box(0);
                        v_isShared_646_ = v_isSharedCheck_650_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_646_ == 0 {
                    v___x_648_ = v___x_645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_649_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
                    v___x_648_ = v_reuseFailAlloc_649_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(
    mut v_k_651_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_652_: *mut crate::leanh::LeanObject,
    mut v___y_653_: *mut crate::leanh::LeanObject,
    mut v___y_654_: *mut crate::leanh::LeanObject,
    mut v___y_655_: *mut crate::leanh::LeanObject,
    mut v___y_656_: *mut crate::leanh::LeanObject,
    mut v___y_657_: *mut crate::leanh::LeanObject,
    mut v___y_658_: *mut crate::leanh::LeanObject,
    mut v___y_659_: *mut crate::leanh::LeanObject,
    mut v___y_660_: *mut crate::leanh::LeanObject,
    mut v___y_661_: *mut crate::leanh::LeanObject,
    mut v___y_662_: *mut crate::leanh::LeanObject,
    mut v___y_663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_664_: u8 = 0;
    let mut v_res_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_664_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_652_) as u8);
    v_res_665_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_651_, v_allowLevelAssignments_boxed_664_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
    crate::leanh::lean_dec(v___y_662_);
    crate::leanh::lean_dec_ref(v___y_661_);
    crate::leanh::lean_dec(v___y_660_);
    crate::leanh::lean_dec_ref(v___y_659_);
    crate::leanh::lean_dec(v___y_658_);
    crate::leanh::lean_dec_ref(v___y_657_);
    crate::leanh::lean_dec(v___y_656_);
    crate::leanh::lean_dec_ref(v___y_655_);
    crate::leanh::lean_dec(v___y_654_);
    crate::leanh::lean_dec(v___y_653_);
    return v_res_665_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(
    mut v_00_u03b1_666_: *mut crate::leanh::LeanObject,
    mut v_k_667_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_668_: u8,
    mut v___y_669_: *mut crate::leanh::LeanObject,
    mut v___y_670_: *mut crate::leanh::LeanObject,
    mut v___y_671_: *mut crate::leanh::LeanObject,
    mut v___y_672_: *mut crate::leanh::LeanObject,
    mut v___y_673_: *mut crate::leanh::LeanObject,
    mut v___y_674_: *mut crate::leanh::LeanObject,
    mut v___y_675_: *mut crate::leanh::LeanObject,
    mut v___y_676_: *mut crate::leanh::LeanObject,
    mut v___y_677_: *mut crate::leanh::LeanObject,
    mut v___y_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_667_, v_allowLevelAssignments_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
    return v___x_680_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___boxed(
    mut v_00_u03b1_681_: *mut crate::leanh::LeanObject,
    mut v_k_682_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_683_: *mut crate::leanh::LeanObject,
    mut v___y_684_: *mut crate::leanh::LeanObject,
    mut v___y_685_: *mut crate::leanh::LeanObject,
    mut v___y_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
    mut v___y_688_: *mut crate::leanh::LeanObject,
    mut v___y_689_: *mut crate::leanh::LeanObject,
    mut v___y_690_: *mut crate::leanh::LeanObject,
    mut v___y_691_: *mut crate::leanh::LeanObject,
    mut v___y_692_: *mut crate::leanh::LeanObject,
    mut v___y_693_: *mut crate::leanh::LeanObject,
    mut v___y_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_695_: u8 = 0;
    let mut v_res_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_695_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_683_) as u8);
    v_res_696_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1(
            v_00_u03b1_681_,
            v_k_682_,
            v_allowLevelAssignments_boxed_695_,
            v___y_684_,
            v___y_685_,
            v___y_686_,
            v___y_687_,
            v___y_688_,
            v___y_689_,
            v___y_690_,
            v___y_691_,
            v___y_692_,
            v___y_693_,
        );
    crate::leanh::lean_dec(v___y_693_);
    crate::leanh::lean_dec_ref(v___y_692_);
    crate::leanh::lean_dec(v___y_691_);
    crate::leanh::lean_dec_ref(v___y_690_);
    crate::leanh::lean_dec(v___y_689_);
    crate::leanh::lean_dec_ref(v___y_688_);
    crate::leanh::lean_dec(v___y_687_);
    crate::leanh::lean_dec_ref(v___y_686_);
    crate::leanh::lean_dec(v___y_685_);
    crate::leanh::lean_dec(v___y_684_);
    return v_res_696_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(
    mut v___x_704_: *mut crate::leanh::LeanObject,
    mut v___x_705_: u8,
    mut v___x_706_: *mut crate::leanh::LeanObject,
    mut v_u_707_: *mut crate::leanh::LeanObject,
    mut v___x_708_: *mut crate::leanh::LeanObject,
    mut v_type_709_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_710_: *mut crate::leanh::LeanObject,
    mut v___y_711_: *mut crate::leanh::LeanObject,
    mut v___y_712_: *mut crate::leanh::LeanObject,
    mut v___y_713_: *mut crate::leanh::LeanObject,
    mut v___y_714_: *mut crate::leanh::LeanObject,
    mut v___y_715_: *mut crate::leanh::LeanObject,
    mut v___y_716_: *mut crate::leanh::LeanObject,
    mut v___y_717_: *mut crate::leanh::LeanObject,
    mut v___y_718_: *mut crate::leanh::LeanObject,
    mut v___y_719_: *mut crate::leanh::LeanObject,
    mut v___y_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charType_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v_val_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v_val_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_744_: u8 = 0;
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v_a_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_761_: u8 = 0;
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_765_: u8 = 0;
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut v_a_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_774_: u8 = 0;
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v_a_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_782_: u8 = 0;
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_722_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_704_, v___x_705_, v___x_706_, v___y_717_, v___y_718_, v___y_719_,
                    v___y_720_,
                );
                if crate::leanh::lean_obj_tag(v___x_722_) == 0 {
                    v_a_723_ = crate::leanh::lean_ctor_get(v___x_722_, 0);
                    crate::leanh::lean_inc_n(v_a_723_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_722_, 1);
                    v___x_724_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__3;
                    v___x_725_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_725_, 0, v_u_707_);
                    crate::leanh::lean_ctor_set(v___x_725_, 1, v___x_708_);
                    v___x_726_ = l_Lean_mkConst(v___x_724_, v___x_725_);
                    v_charType_727_ =
                        l_Lean_mkApp3(v___x_726_, v_type_709_, v_semiringInst_710_, v_a_723_);
                    v___x_728_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v_charType_727_,
                        v___y_717_,
                        v___y_718_,
                        v___y_719_,
                        v___y_720_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_728_) == 0 {
                        v_a_729_ = crate::leanh::lean_ctor_get(v___x_728_, 0);
                        v_isSharedCheck_770_ = (!crate::leanh::lean_is_exclusive(v___x_728_)) as u8;
                        if v_isSharedCheck_770_ == 0 {
                            v___x_731_ = v___x_728_;
                            v_isShared_732_ = v_isSharedCheck_770_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_729_);
                            crate::leanh::lean_dec(v___x_728_);
                            v___x_731_ = crate::leanh::lean_box(0);
                            v_isShared_732_ = v_isSharedCheck_770_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_723_);
                        v_a_771_ = crate::leanh::lean_ctor_get(v___x_728_, 0);
                        v_isSharedCheck_778_ = (!crate::leanh::lean_is_exclusive(v___x_728_)) as u8;
                        if v_isSharedCheck_778_ == 0 {
                            v___x_773_ = v___x_728_;
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_771_);
                            crate::leanh::lean_dec(v___x_728_);
                            v___x_773_ = crate::leanh::lean_box(0);
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_semiringInst_710_);
                    crate::leanh::lean_dec_ref(v_type_709_);
                    crate::leanh::lean_dec(v___x_708_);
                    crate::leanh::lean_dec(v_u_707_);
                    v_a_779_ = crate::leanh::lean_ctor_get(v___x_722_, 0);
                    v_isSharedCheck_786_ = (!crate::leanh::lean_is_exclusive(v___x_722_)) as u8;
                    if v_isSharedCheck_786_ == 0 {
                        v___x_781_ = v___x_722_;
                        v_isShared_782_ = v_isSharedCheck_786_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_779_);
                        crate::leanh::lean_dec(v___x_722_);
                        v___x_781_ = crate::leanh::lean_box(0);
                        v_isShared_782_ = v_isSharedCheck_786_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_729_) == 1 {
                    crate::leanh::lean_del_object(v___x_731_);
                    v_val_733_ = crate::leanh::lean_ctor_get(v_a_729_, 0);
                    crate::leanh::lean_inc(v_val_733_);
                    crate::leanh::lean_dec_ref_known(v_a_729_, 1);
                    v___x_734_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_723_, v___y_718_);
                    v_a_735_ = crate::leanh::lean_ctor_get(v___x_734_, 0);
                    crate::leanh::lean_inc(v_a_735_);
                    crate::leanh::lean_dec_ref(v___x_734_);
                    v___x_736_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(
                        v_a_735_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_,
                        v___y_717_, v___y_718_, v___y_719_, v___y_720_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_736_) == 0 {
                        v_a_737_ = crate::leanh::lean_ctor_get(v___x_736_, 0);
                        v_isSharedCheck_757_ = (!crate::leanh::lean_is_exclusive(v___x_736_)) as u8;
                        if v_isSharedCheck_757_ == 0 {
                            v___x_739_ = v___x_736_;
                            v_isShared_740_ = v_isSharedCheck_757_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_737_);
                            crate::leanh::lean_dec(v___x_736_);
                            v___x_739_ = crate::leanh::lean_box(0);
                            v_isShared_740_ = v_isSharedCheck_757_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_733_);
                        v_a_758_ = crate::leanh::lean_ctor_get(v___x_736_, 0);
                        v_isSharedCheck_765_ = (!crate::leanh::lean_is_exclusive(v___x_736_)) as u8;
                        if v_isSharedCheck_765_ == 0 {
                            v___x_760_ = v___x_736_;
                            v_isShared_761_ = v_isSharedCheck_765_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_758_);
                            crate::leanh::lean_dec(v___x_736_);
                            v___x_760_ = crate::leanh::lean_box(0);
                            v_isShared_761_ = v_isSharedCheck_765_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_729_);
                    crate::leanh::lean_dec(v_a_723_);
                    v___x_766_ = crate::leanh::lean_box(0);
                    if v_isShared_732_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_731_, 0, v___x_766_);
                        v___x_768_ = v___x_731_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
                        v___x_768_ = v_reuseFailAlloc_769_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_737_) == 1 {
                    v_val_741_ = crate::leanh::lean_ctor_get(v_a_737_, 0);
                    v_isSharedCheck_752_ = (!crate::leanh::lean_is_exclusive(v_a_737_)) as u8;
                    if v_isSharedCheck_752_ == 0 {
                        v___x_743_ = v_a_737_;
                        v_isShared_744_ = v_isSharedCheck_752_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_741_);
                        crate::leanh::lean_dec(v_a_737_);
                        v___x_743_ = crate::leanh::lean_box(0);
                        v_isShared_744_ = v_isSharedCheck_752_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_737_);
                    crate::leanh::lean_dec(v_val_733_);
                    v___x_753_ = crate::leanh::lean_box(0);
                    if v_isShared_740_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_739_, 0, v___x_753_);
                        v___x_755_ = v___x_739_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
                        v___x_755_ = v_reuseFailAlloc_756_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_745_, 0, v_val_733_);
                crate::leanh::lean_ctor_set(v___x_745_, 1, v_val_741_);
                if v_isShared_744_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_743_, 0, v___x_745_);
                    v___x_747_ = v___x_743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_745_);
                    v___x_747_ = v_reuseFailAlloc_751_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_739_, 0, v___x_747_);
                    v___x_749_ = v___x_739_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
                    v___x_749_ = v_reuseFailAlloc_750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_749_;
            }
            6 => {
                return v___x_755_;
            }
            7 => {
                if v_isShared_761_ == 0 {
                    v___x_763_ = v___x_760_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
                    v___x_763_ = v_reuseFailAlloc_764_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_763_;
            }
            9 => {
                return v___x_768_;
            }
            10 => {
                if v_isShared_774_ == 0 {
                    v___x_776_ = v___x_773_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
                    v___x_776_ = v_reuseFailAlloc_777_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_776_;
            }
            12 => {
                if v_isShared_782_ == 0 {
                    v___x_784_ = v___x_781_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
                    v___x_784_ = v_reuseFailAlloc_785_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_787_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_788_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_789_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_u_790_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_791_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_type_792_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_semiringInst_793_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_794_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_795_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_796_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_797_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_798_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_799_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_800_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_801_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_802_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_803_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_804_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_9036__boxed_805_: u8 = 0;
    let mut v_res_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9036__boxed_805_ = (crate::leanh::lean_unbox(v___x_788_) as u8);
    v_res_806_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0(
        v___x_787_,
        v___x_9036__boxed_805_,
        v___x_789_,
        v_u_790_,
        v___x_791_,
        v_type_792_,
        v_semiringInst_793_,
        v___y_794_,
        v___y_795_,
        v___y_796_,
        v___y_797_,
        v___y_798_,
        v___y_799_,
        v___y_800_,
        v___y_801_,
        v___y_802_,
        v___y_803_,
    );
    crate::leanh::lean_dec(v___y_803_);
    crate::leanh::lean_dec_ref(v___y_802_);
    crate::leanh::lean_dec(v___y_801_);
    crate::leanh::lean_dec_ref(v___y_800_);
    crate::leanh::lean_dec(v___y_799_);
    crate::leanh::lean_dec_ref(v___y_798_);
    crate::leanh::lean_dec(v___y_797_);
    crate::leanh::lean_dec_ref(v___y_796_);
    crate::leanh::lean_dec(v___y_795_);
    crate::leanh::lean_dec(v___y_794_);
    return v_res_806_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = crate::leanh::lean_box(0);
    v___x_811_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1;
    v___x_812_ = l_Lean_mkConst(v___x_811_, v___x_810_);
    return v___x_812_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2_once),
        _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__2,
    );
    v___x_814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_814_, 0, v___x_813_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(
    mut v_u_815_: *mut crate::leanh::LeanObject,
    mut v_type_816_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_817_: *mut crate::leanh::LeanObject,
    mut v_a_818_: *mut crate::leanh::LeanObject,
    mut v_a_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: u8 = 0;
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: u8 = 0;
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = crate::leanh::lean_box(0);
    v___x_830_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3_once),
        _init_l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__3,
    );
    v___x_831_ = 0;
    v___x_832_ = crate::leanh::lean_box(0);
    v___x_833_ = crate::leanh::lean_box((v___x_831_) as usize);
    v___f_834_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___boxed as *mut core::ffi::c_void,
        18,
        7,
    );
    crate::leanh::lean_closure_set(v___f_834_, 0, v___x_830_);
    crate::leanh::lean_closure_set(v___f_834_, 1, v___x_833_);
    crate::leanh::lean_closure_set(v___f_834_, 2, v___x_832_);
    crate::leanh::lean_closure_set(v___f_834_, 3, v_u_815_);
    crate::leanh::lean_closure_set(v___f_834_, 4, v___x_829_);
    crate::leanh::lean_closure_set(v___f_834_, 5, v_type_816_);
    crate::leanh::lean_closure_set(v___f_834_, 6, v_semiringInst_817_);
    v___x_835_ = 0;
    v___x_836_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_834_, v___x_835_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
    return v___x_836_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___boxed(
    mut v_u_837_: *mut crate::leanh::LeanObject,
    mut v_type_838_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_a_846_: *mut crate::leanh::LeanObject,
    mut v_a_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_851_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f(
        v_u_837_,
        v_type_838_,
        v_semiringInst_839_,
        v_a_840_,
        v_a_841_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
        v_a_847_,
        v_a_848_,
        v_a_849_,
    );
    crate::leanh::lean_dec(v_a_849_);
    crate::leanh::lean_dec_ref(v_a_848_);
    crate::leanh::lean_dec(v_a_847_);
    crate::leanh::lean_dec_ref(v_a_846_);
    crate::leanh::lean_dec(v_a_845_);
    crate::leanh::lean_dec_ref(v_a_844_);
    crate::leanh::lean_dec(v_a_843_);
    crate::leanh::lean_dec_ref(v_a_842_);
    crate::leanh::lean_dec(v_a_841_);
    crate::leanh::lean_dec(v_a_840_);
    return v_res_851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0(
    mut v___x_853_: *mut crate::leanh::LeanObject,
    mut v___x_854_: u8,
    mut v___x_855_: *mut crate::leanh::LeanObject,
    mut v___x_856_: *mut crate::leanh::LeanObject,
    mut v___x_857_: *mut crate::leanh::LeanObject,
    mut v___x_858_: *mut crate::leanh::LeanObject,
    mut v___x_859_: *mut crate::leanh::LeanObject,
    mut v_type_860_: *mut crate::leanh::LeanObject,
    mut v___y_861_: *mut crate::leanh::LeanObject,
    mut v___y_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
    mut v___y_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
    mut v___y_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
    mut v___y_869_: *mut crate::leanh::LeanObject,
    mut v___y_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v_val_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v_val_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_901_: u8 = 0;
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_910_: u8 = 0;
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_915_: u8 = 0;
    let mut v_a_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_923_: u8 = 0;
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_928_: u8 = 0;
    let mut v_a_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_932_: u8 = 0;
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_936_: u8 = 0;
    let mut v_a_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_944_: u8 = 0;
    let mut v_a_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_855_);
                v___x_872_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_853_, v___x_854_, v___x_855_, v___y_867_, v___y_868_, v___y_869_,
                    v___y_870_,
                );
                if crate::leanh::lean_obj_tag(v___x_872_) == 0 {
                    v_a_873_ = crate::leanh::lean_ctor_get(v___x_872_, 0);
                    crate::leanh::lean_inc(v_a_873_);
                    crate::leanh::lean_dec_ref_known(v___x_872_, 1);
                    v___x_874_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___closed__1;
                    v___x_875_ = l_Lean_mkConst(v___x_874_, v___x_856_);
                    v___x_876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_876_, 0, v___x_875_);
                    v___x_877_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_876_, v___x_854_, v___x_855_, v___y_867_, v___y_868_, v___y_869_,
                        v___y_870_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_877_) == 0 {
                        v_a_878_ = crate::leanh::lean_ctor_get(v___x_877_, 0);
                        crate::leanh::lean_inc_n(v_a_878_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_877_, 1);
                        v___x_879_ =
                            l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___closed__0;
                        v___x_880_ = l_Lean_Name_mkStr3(v___x_857_, v___x_858_, v___x_879_);
                        v___x_881_ = l_Lean_mkConst(v___x_880_, v___x_859_);
                        crate::leanh::lean_inc(v_a_873_);
                        v___x_882_ = l_Lean_mkApp3(v___x_881_, v_type_860_, v_a_873_, v_a_878_);
                        v___x_883_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                            v___x_882_, v___y_867_, v___y_868_, v___y_869_, v___y_870_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_883_) == 0 {
                            v_a_884_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                            v_isSharedCheck_928_ =
                                (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                            if v_isSharedCheck_928_ == 0 {
                                v___x_886_ = v___x_883_;
                                v_isShared_887_ = v_isSharedCheck_928_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_884_);
                                crate::leanh::lean_dec(v___x_883_);
                                v___x_886_ = crate::leanh::lean_box(0);
                                v_isShared_887_ = v_isSharedCheck_928_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_878_);
                            crate::leanh::lean_dec(v_a_873_);
                            v_a_929_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                            v_isSharedCheck_936_ =
                                (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                            if v_isSharedCheck_936_ == 0 {
                                v___x_931_ = v___x_883_;
                                v_isShared_932_ = v_isSharedCheck_936_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_929_);
                                crate::leanh::lean_dec(v___x_883_);
                                v___x_931_ = crate::leanh::lean_box(0);
                                v_isShared_932_ = v_isSharedCheck_936_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_873_);
                        crate::leanh::lean_dec_ref(v_type_860_);
                        crate::leanh::lean_dec(v___x_859_);
                        crate::leanh::lean_dec_ref(v___x_858_);
                        crate::leanh::lean_dec_ref(v___x_857_);
                        v_a_937_ = crate::leanh::lean_ctor_get(v___x_877_, 0);
                        v_isSharedCheck_944_ = (!crate::leanh::lean_is_exclusive(v___x_877_)) as u8;
                        if v_isSharedCheck_944_ == 0 {
                            v___x_939_ = v___x_877_;
                            v_isShared_940_ = v_isSharedCheck_944_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_937_);
                            crate::leanh::lean_dec(v___x_877_);
                            v___x_939_ = crate::leanh::lean_box(0);
                            v_isShared_940_ = v_isSharedCheck_944_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_860_);
                    crate::leanh::lean_dec(v___x_859_);
                    crate::leanh::lean_dec_ref(v___x_858_);
                    crate::leanh::lean_dec_ref(v___x_857_);
                    crate::leanh::lean_dec(v___x_856_);
                    crate::leanh::lean_dec(v___x_855_);
                    v_a_945_ = crate::leanh::lean_ctor_get(v___x_872_, 0);
                    v_isSharedCheck_952_ = (!crate::leanh::lean_is_exclusive(v___x_872_)) as u8;
                    if v_isSharedCheck_952_ == 0 {
                        v___x_947_ = v___x_872_;
                        v_isShared_948_ = v_isSharedCheck_952_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_945_);
                        crate::leanh::lean_dec(v___x_872_);
                        v___x_947_ = crate::leanh::lean_box(0);
                        v_isShared_948_ = v_isSharedCheck_952_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_884_) == 1 {
                    crate::leanh::lean_del_object(v___x_886_);
                    v_val_888_ = crate::leanh::lean_ctor_get(v_a_884_, 0);
                    crate::leanh::lean_inc(v_val_888_);
                    crate::leanh::lean_dec_ref_known(v_a_884_, 1);
                    v___x_889_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_873_, v___y_868_);
                    v_a_890_ = crate::leanh::lean_ctor_get(v___x_889_, 0);
                    crate::leanh::lean_inc(v_a_890_);
                    crate::leanh::lean_dec_ref(v___x_889_);
                    v___x_891_ = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_878_, v___y_868_);
                    v_a_892_ = crate::leanh::lean_ctor_get(v___x_891_, 0);
                    crate::leanh::lean_inc(v_a_892_);
                    crate::leanh::lean_dec_ref(v___x_891_);
                    v___x_893_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(
                        v_a_892_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_,
                        v___y_867_, v___y_868_, v___y_869_, v___y_870_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_893_) == 0 {
                        v_a_894_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                        v_isSharedCheck_915_ = (!crate::leanh::lean_is_exclusive(v___x_893_)) as u8;
                        if v_isSharedCheck_915_ == 0 {
                            v___x_896_ = v___x_893_;
                            v_isShared_897_ = v_isSharedCheck_915_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_894_);
                            crate::leanh::lean_dec(v___x_893_);
                            v___x_896_ = crate::leanh::lean_box(0);
                            v_isShared_897_ = v_isSharedCheck_915_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_890_);
                        crate::leanh::lean_dec(v_val_888_);
                        v_a_916_ = crate::leanh::lean_ctor_get(v___x_893_, 0);
                        v_isSharedCheck_923_ = (!crate::leanh::lean_is_exclusive(v___x_893_)) as u8;
                        if v_isSharedCheck_923_ == 0 {
                            v___x_918_ = v___x_893_;
                            v_isShared_919_ = v_isSharedCheck_923_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_916_);
                            crate::leanh::lean_dec(v___x_893_);
                            v___x_918_ = crate::leanh::lean_box(0);
                            v_isShared_919_ = v_isSharedCheck_923_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_884_);
                    crate::leanh::lean_dec(v_a_878_);
                    crate::leanh::lean_dec(v_a_873_);
                    v___x_924_ = crate::leanh::lean_box(0);
                    if v_isShared_887_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_886_, 0, v___x_924_);
                        v___x_926_ = v___x_886_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
                        v___x_926_ = v_reuseFailAlloc_927_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_894_) == 1 {
                    v_val_898_ = crate::leanh::lean_ctor_get(v_a_894_, 0);
                    v_isSharedCheck_910_ = (!crate::leanh::lean_is_exclusive(v_a_894_)) as u8;
                    if v_isSharedCheck_910_ == 0 {
                        v___x_900_ = v_a_894_;
                        v_isShared_901_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_898_);
                        crate::leanh::lean_dec(v_a_894_);
                        v___x_900_ = crate::leanh::lean_box(0);
                        v_isShared_901_ = v_isSharedCheck_910_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_894_);
                    crate::leanh::lean_dec(v_a_890_);
                    crate::leanh::lean_dec(v_val_888_);
                    v___x_911_ = crate::leanh::lean_box(0);
                    if v_isShared_897_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_911_);
                        v___x_913_ = v___x_896_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
                        v___x_913_ = v_reuseFailAlloc_914_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_902_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_902_, 0, v_a_890_);
                crate::leanh::lean_ctor_set(v___x_902_, 1, v_val_898_);
                v___x_903_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_903_, 0, v_val_888_);
                crate::leanh::lean_ctor_set(v___x_903_, 1, v___x_902_);
                if v_isShared_901_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_900_, 0, v___x_903_);
                    v___x_905_ = v___x_900_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_903_);
                    v___x_905_ = v_reuseFailAlloc_909_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_905_);
                    v___x_907_ = v___x_896_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
                    v___x_907_ = v_reuseFailAlloc_908_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_907_;
            }
            6 => {
                return v___x_913_;
            }
            7 => {
                if v_isShared_919_ == 0 {
                    v___x_921_ = v___x_918_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_922_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
                    v___x_921_ = v_reuseFailAlloc_922_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_921_;
            }
            9 => {
                return v___x_926_;
            }
            10 => {
                if v_isShared_932_ == 0 {
                    v___x_934_ = v___x_931_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_935_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
                    v___x_934_ = v_reuseFailAlloc_935_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_934_;
            }
            12 => {
                if v_isShared_940_ == 0 {
                    v___x_942_ = v___x_939_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
                    v___x_942_ = v_reuseFailAlloc_943_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_942_;
            }
            14 => {
                if v_isShared_948_ == 0 {
                    v___x_950_ = v___x_947_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
                    v___x_950_ = v_reuseFailAlloc_951_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_953_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_954_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_955_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_956_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_957_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_958_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_959_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_type_960_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_961_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_962_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_963_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_964_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_965_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_966_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_967_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_968_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_969_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_970_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_971_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_6988__boxed_972_: u8 = 0;
    let mut v_res_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6988__boxed_972_ = (crate::leanh::lean_unbox(v___x_954_) as u8);
    v_res_973_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0(
        v___x_953_,
        v___x_6988__boxed_972_,
        v___x_955_,
        v___x_956_,
        v___x_957_,
        v___x_958_,
        v___x_959_,
        v_type_960_,
        v___y_961_,
        v___y_962_,
        v___y_963_,
        v___y_964_,
        v___y_965_,
        v___y_966_,
        v___y_967_,
        v___y_968_,
        v___y_969_,
        v___y_970_,
    );
    crate::leanh::lean_dec(v___y_970_);
    crate::leanh::lean_dec_ref(v___y_969_);
    crate::leanh::lean_dec(v___y_968_);
    crate::leanh::lean_dec_ref(v___y_967_);
    crate::leanh::lean_dec(v___y_966_);
    crate::leanh::lean_dec_ref(v___y_965_);
    crate::leanh::lean_dec(v___y_964_);
    crate::leanh::lean_dec_ref(v___y_963_);
    crate::leanh::lean_dec(v___y_962_);
    crate::leanh::lean_dec(v___y_961_);
    return v_res_973_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(
    mut v_u_979_: *mut crate::leanh::LeanObject,
    mut v_type_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v_a_983_: *mut crate::leanh::LeanObject,
    mut v_a_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
    mut v_a_986_: *mut crate::leanh::LeanObject,
    mut v_a_987_: *mut crate::leanh::LeanObject,
    mut v_a_988_: *mut crate::leanh::LeanObject,
    mut v_a_989_: *mut crate::leanh::LeanObject,
    mut v_a_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__0;
    v___x_993_ = l_Lean_Meta_Grind_Arith_getIsCharInst_x3f___lam__0___closed__1;
    v___x_994_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___closed__1;
    v___x_995_ = crate::leanh::lean_box(0);
    v___x_996_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_996_, 0, v_u_979_);
    crate::leanh::lean_ctor_set(v___x_996_, 1, v___x_995_);
    crate::leanh::lean_inc_ref(v___x_996_);
    v___x_997_ = l_Lean_mkConst(v___x_994_, v___x_996_);
    crate::leanh::lean_inc_ref(v_type_980_);
    v___x_998_ = l_Lean_Expr_app___override(v___x_997_, v_type_980_);
    v___x_999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_999_, 0, v___x_998_);
    v___x_1000_ = 0;
    v___x_1001_ = crate::leanh::lean_box(0);
    v___x_1002_ = crate::leanh::lean_box((v___x_1000_) as usize);
    v___f_1003_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___lam__0___boxed as *mut core::ffi::c_void,
        19,
        8,
    );
    crate::leanh::lean_closure_set(v___f_1003_, 0, v___x_999_);
    crate::leanh::lean_closure_set(v___f_1003_, 1, v___x_1002_);
    crate::leanh::lean_closure_set(v___f_1003_, 2, v___x_1001_);
    crate::leanh::lean_closure_set(v___f_1003_, 3, v___x_995_);
    crate::leanh::lean_closure_set(v___f_1003_, 4, v___x_992_);
    crate::leanh::lean_closure_set(v___f_1003_, 5, v___x_993_);
    crate::leanh::lean_closure_set(v___f_1003_, 6, v___x_996_);
    crate::leanh::lean_closure_set(v___f_1003_, 7, v_type_980_);
    v___x_1004_ = 0;
    v___x_1005_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_1003_, v___x_1004_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
    return v___x_1005_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f___boxed(
    mut v_u_1006_: *mut crate::leanh::LeanObject,
    mut v_type_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
    mut v_a_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
    mut v_a_1017_: *mut crate::leanh::LeanObject,
    mut v_a_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Lean_Meta_Grind_Arith_getPowIdentityInst_x3f(
        v_u_1006_,
        v_type_1007_,
        v_a_1008_,
        v_a_1009_,
        v_a_1010_,
        v_a_1011_,
        v_a_1012_,
        v_a_1013_,
        v_a_1014_,
        v_a_1015_,
        v_a_1016_,
        v_a_1017_,
    );
    crate::leanh::lean_dec(v_a_1017_);
    crate::leanh::lean_dec_ref(v_a_1016_);
    crate::leanh::lean_dec(v_a_1015_);
    crate::leanh::lean_dec_ref(v_a_1014_);
    crate::leanh::lean_dec(v_a_1013_);
    crate::leanh::lean_dec_ref(v_a_1012_);
    crate::leanh::lean_dec(v_a_1011_);
    crate::leanh::lean_dec_ref(v_a_1010_);
    crate::leanh::lean_dec(v_a_1009_);
    crate::leanh::lean_dec(v_a_1008_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
    mut v_u_1030_: *mut crate::leanh::LeanObject,
    mut v_type_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
    mut v_a_1033_: *mut crate::leanh::LeanObject,
    mut v_a_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleType_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1046_: u8 = 0;
    let mut v_val_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1037_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__1;
                v___x_1038_ = crate::leanh::lean_box(0);
                v___x_1039_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1039_, 0, v_u_1030_);
                crate::leanh::lean_ctor_set(v___x_1039_, 1, v___x_1038_);
                crate::leanh::lean_inc_ref(v___x_1039_);
                v___x_1040_ = l_Lean_mkConst(v___x_1037_, v___x_1039_);
                crate::leanh::lean_inc_ref(v_type_1031_);
                v_natModuleType_1041_ = l_Lean_Expr_app___override(v___x_1040_, v_type_1031_);
                v___x_1042_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_natModuleType_1041_,
                    v_a_1032_,
                    v_a_1033_,
                    v_a_1034_,
                    v_a_1035_,
                );
                if crate::leanh::lean_obj_tag(v___x_1042_) == 0 {
                    v_a_1043_ = crate::leanh::lean_ctor_get(v___x_1042_, 0);
                    v_isSharedCheck_1056_ = (!crate::leanh::lean_is_exclusive(v___x_1042_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1045_ = v___x_1042_;
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1043_);
                        crate::leanh::lean_dec(v___x_1042_);
                        v___x_1045_ = crate::leanh::lean_box(0);
                        v_isShared_1046_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1039_, 2);
                    crate::leanh::lean_dec_ref(v_type_1031_);
                    return v___x_1042_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1043_) == 1 {
                    crate::leanh::lean_del_object(v___x_1045_);
                    v_val_1047_ = crate::leanh::lean_ctor_get(v_a_1043_, 0);
                    crate::leanh::lean_inc(v_val_1047_);
                    crate::leanh::lean_dec_ref_known(v_a_1043_, 1);
                    v___x_1048_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___closed__3;
                    v___x_1049_ = l_Lean_mkConst(v___x_1048_, v___x_1039_);
                    v___x_1050_ = l_Lean_mkAppB(v___x_1049_, v_type_1031_, v_val_1047_);
                    v___x_1051_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_1050_,
                        v_a_1032_,
                        v_a_1033_,
                        v_a_1034_,
                        v_a_1035_,
                    );
                    return v___x_1051_;
                } else {
                    crate::leanh::lean_dec(v_a_1043_);
                    crate::leanh::lean_dec_ref_known(v___x_1039_, 2);
                    crate::leanh::lean_dec_ref(v_type_1031_);
                    v___x_1052_ = crate::leanh::lean_box(0);
                    if v_isShared_1046_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1045_, 0, v___x_1052_);
                        v___x_1054_ = v___x_1045_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
                        v___x_1054_ = v_reuseFailAlloc_1055_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1054_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg___boxed(
    mut v_u_1057_: *mut crate::leanh::LeanObject,
    mut v_type_1058_: *mut crate::leanh::LeanObject,
    mut v_a_1059_: *mut crate::leanh::LeanObject,
    mut v_a_1060_: *mut crate::leanh::LeanObject,
    mut v_a_1061_: *mut crate::leanh::LeanObject,
    mut v_a_1062_: *mut crate::leanh::LeanObject,
    mut v_a_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
        v_u_1057_,
        v_type_1058_,
        v_a_1059_,
        v_a_1060_,
        v_a_1061_,
        v_a_1062_,
    );
    crate::leanh::lean_dec(v_a_1062_);
    crate::leanh::lean_dec_ref(v_a_1061_);
    crate::leanh::lean_dec(v_a_1060_);
    crate::leanh::lean_dec_ref(v_a_1059_);
    return v_res_1064_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(
    mut v_u_1065_: *mut crate::leanh::LeanObject,
    mut v_type_1066_: *mut crate::leanh::LeanObject,
    mut v_a_1067_: *mut crate::leanh::LeanObject,
    mut v_a_1068_: *mut crate::leanh::LeanObject,
    mut v_a_1069_: *mut crate::leanh::LeanObject,
    mut v_a_1070_: *mut crate::leanh::LeanObject,
    mut v_a_1071_: *mut crate::leanh::LeanObject,
    mut v_a_1072_: *mut crate::leanh::LeanObject,
    mut v_a_1073_: *mut crate::leanh::LeanObject,
    mut v_a_1074_: *mut crate::leanh::LeanObject,
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___redArg(
        v_u_1065_,
        v_type_1066_,
        v_a_1073_,
        v_a_1074_,
        v_a_1075_,
        v_a_1076_,
    );
    return v___x_1078_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f___boxed(
    mut v_u_1079_: *mut crate::leanh::LeanObject,
    mut v_type_1080_: *mut crate::leanh::LeanObject,
    mut v_a_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
    mut v_a_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_a_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Lean_Meta_Grind_Arith_getNoZeroDivInst_x3f(
        v_u_1079_,
        v_type_1080_,
        v_a_1081_,
        v_a_1082_,
        v_a_1083_,
        v_a_1084_,
        v_a_1085_,
        v_a_1086_,
        v_a_1087_,
        v_a_1088_,
        v_a_1089_,
        v_a_1090_,
    );
    crate::leanh::lean_dec(v_a_1090_);
    crate::leanh::lean_dec_ref(v_a_1089_);
    crate::leanh::lean_dec(v_a_1088_);
    crate::leanh::lean_dec_ref(v_a_1087_);
    crate::leanh::lean_dec(v_a_1086_);
    crate::leanh::lean_dec_ref(v_a_1085_);
    crate::leanh::lean_dec(v_a_1084_);
    crate::leanh::lean_dec_ref(v_a_1083_);
    crate::leanh::lean_dec(v_a_1082_);
    crate::leanh::lean_dec(v_a_1081_);
    return v_res_1092_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Insts(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Insts(builtin);
}
