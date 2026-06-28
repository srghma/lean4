// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical
// Imports: Lean.Meta.Tactic.BVDecide.Reflect.Reify
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_mkStr6,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Basic::{
    l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::ReifiedBVLogical::{
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::Reflect::Reify::{
    initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify,
    l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of,
    runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::lean_imports_rs::Init::Prelude::lean_nat_dec_eq;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0_value: LeanStringObject<3> =
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
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value: LeanStringObject<5> =
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
        m_data: [66, 111, 111, 108, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4_value: LeanStringObject<5> =
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
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value)
                as *mut LeanObject,
            12882480457794858234 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4_value)
                as *mut LeanObject,
            9255189395584251158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4_value:
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
    m_data: [115, 97, 116, 95, 97, 110, 100, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value
        ) as *mut LeanObject,
        15170596904992606634 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4_value
        ) as *mut LeanObject,
        7039433608906007325 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0_value: LeanStringObject<9> =
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
        m_data: [66, 111, 111, 108, 69, 120, 112, 114, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1_value: LeanStringObject<5> =
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
        m_data: [103, 97, 116, 101, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value
            ) as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value
            ) as *mut LeanObject,
            5139300886809190733 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value
            ) as *mut LeanObject,
            17363264175708149920 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_3: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0_value)
                as *mut LeanObject,
            5051218143360974414 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1_value)
                as *mut LeanObject,
            16066464032356577345 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4_value: LeanStringObject<7> =
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
        m_data: [66, 86, 80, 114, 101, 100, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value
            ) as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value
            ) as *mut LeanObject,
            5139300886809190733 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value
            ) as *mut LeanObject,
            17363264175708149920 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4_value)
                as *mut LeanObject,
            18198180362361044236 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7_value: LeanStringObject<5> =
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
        m_data: [71, 97, 116, 101, 0],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8_value: LeanStringObject<4> =
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
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value
            ) as *mut LeanObject,
            15734321041234825264 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value
            ) as *mut LeanObject,
            5139300886809190733 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value
            ) as *mut LeanObject,
            17363264175708149920 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_3: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7_value)
                as *mut LeanObject,
            13347281081598155225 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_3
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8_value)
                as *mut LeanObject,
            8714298000618519999 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value:
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
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value
        ) as *mut LeanObject,
        15170596904992606634 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value: LeanCtorObject<
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value)
            as *mut LeanObject,
        13807464631116737617 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value:
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
    m_data: [82, 101, 102, 108, 101, 99, 116, 0],
};
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value:
    LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        102, 97, 108, 115, 101, 95, 111, 102, 95, 101, 113, 95, 116, 114, 117, 101, 95, 111, 102,
        95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value)
        as *mut LeanObject;
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_0:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_1:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value
        ) as *mut LeanObject,
        5139300886809190733 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_2:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value
        ) as *mut LeanObject,
        17363264175708149920 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_3:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value)
            as *mut LeanObject,
        18076273821967539232 as *mut LeanObject,
    ],
};
static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_4:
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_3
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value)
            as *mut LeanObject,
        7340257369084348989 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value: LeanCtorObject<
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
            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_4
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value)
            as *mut LeanObject,
        14085791353490074582 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        85, 110, 97, 98, 108, 101, 32, 116, 111, 32, 105, 100, 101, 110, 116, 105, 102, 121, 32,
        97, 110, 121, 32, 114, 101, 108, 101, 118, 97, 110, 116, 32, 97, 116, 111, 109, 115, 46, 0,
    ],
};
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(
    mut v_e_462_: *mut LeanObject,
    mut v___y_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_479_: u8 = 0;
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_485_: u8 = 0;
    let mut v_unused_486_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_465_ = l_Lean_Expr_hasMVar(v_e_462_);
                if v___x_465_ == 0 {
                    v___x_466_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_466_, 0, v_e_462_);
                    return v___x_466_;
                } else {
                    v___x_467_ = lean_st_ref_get(v___y_463_);
                    v_mctx_468_ = lean_ctor_get(v___x_467_, 0);
                    lean_inc_ref(v_mctx_468_);
                    lean_dec(v___x_467_);
                    v___x_469_ = l_Lean_instantiateMVarsCore(v_mctx_468_, v_e_462_);
                    v_fst_470_ = lean_ctor_get(v___x_469_, 0);
                    lean_inc(v_fst_470_);
                    v_snd_471_ = lean_ctor_get(v___x_469_, 1);
                    lean_inc(v_snd_471_);
                    lean_dec_ref(v___x_469_);
                    v___x_472_ = lean_st_ref_take(v___y_463_);
                    v_cache_473_ = lean_ctor_get(v___x_472_, 1);
                    v_zetaDeltaFVarIds_474_ = lean_ctor_get(v___x_472_, 2);
                    v_postponed_475_ = lean_ctor_get(v___x_472_, 3);
                    v_diag_476_ = lean_ctor_get(v___x_472_, 4);
                    v_isSharedCheck_485_ = (!lean_is_exclusive(v___x_472_)) as u8;
                    if v_isSharedCheck_485_ == 0 {
                        v_unused_486_ = lean_ctor_get(v___x_472_, 0);
                        lean_dec(v_unused_486_);
                        v___x_478_ = v___x_472_;
                        v_isShared_479_ = v_isSharedCheck_485_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_476_);
                        lean_inc(v_postponed_475_);
                        lean_inc(v_zetaDeltaFVarIds_474_);
                        lean_inc(v_cache_473_);
                        lean_dec(v___x_472_);
                        v___x_478_ = lean_box(0);
                        v_isShared_479_ = v_isSharedCheck_485_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_479_ == 0 {
                    lean_ctor_set(v___x_478_, 0, v_snd_471_);
                    v___x_481_ = v___x_478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_484_, 0, v_snd_471_);
                    lean_ctor_set(v_reuseFailAlloc_484_, 1, v_cache_473_);
                    lean_ctor_set(v_reuseFailAlloc_484_, 2, v_zetaDeltaFVarIds_474_);
                    lean_ctor_set(v_reuseFailAlloc_484_, 3, v_postponed_475_);
                    lean_ctor_set(v_reuseFailAlloc_484_, 4, v_diag_476_);
                    v___x_481_ = v_reuseFailAlloc_484_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_482_ = lean_st_ref_set(v___y_463_, v___x_481_);
                v___x_483_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_483_, 0, v_fst_470_);
                return v___x_483_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg___boxed(
    mut v_e_487_: *mut LeanObject,
    mut v___y_488_: *mut LeanObject,
    mut v___y_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_490_: *mut LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(v_e_487_, v___y_488_);
    lean_dec(v___y_488_);
    return v_res_490_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0(
    mut v_e_491_: *mut LeanObject,
    mut v___y_492_: *mut LeanObject,
    mut v___y_493_: *mut LeanObject,
    mut v___y_494_: *mut LeanObject,
    mut v___y_495_: *mut LeanObject,
    mut v___y_496_: *mut LeanObject,
    mut v___y_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(v_e_491_, v___y_495_);
    return v___x_499_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___boxed(
    mut v_e_500_: *mut LeanObject,
    mut v___y_501_: *mut LeanObject,
    mut v___y_502_: *mut LeanObject,
    mut v___y_503_: *mut LeanObject,
    mut v___y_504_: *mut LeanObject,
    mut v___y_505_: *mut LeanObject,
    mut v___y_506_: *mut LeanObject,
    mut v___y_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_508_: *mut LeanObject = core::ptr::null_mut();
    v_res_508_ =
        l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0(
            v_e_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_,
        );
    lean_dec(v___y_506_);
    lean_dec_ref(v___y_505_);
    lean_dec(v___y_504_);
    lean_dec_ref(v___y_503_);
    lean_dec(v___y_502_);
    lean_dec(v___y_501_);
    return v_res_508_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(
    mut v_expr_509_: *mut LeanObject,
    mut v_val_510_: *mut LeanObject,
    mut v___x_511_: *mut LeanObject,
    mut v_arg_512_: *mut LeanObject,
    mut v_h_513_: *mut LeanObject,
    mut v___y_514_: *mut LeanObject,
    mut v___y_515_: *mut LeanObject,
    mut v___y_516_: *mut LeanObject,
    mut v___y_517_: *mut LeanObject,
    mut v___y_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_526_: u8 = 0;
    let mut v___y_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_537_: u8 = 0;
    let mut v_a_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_541_: u8 = 0;
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_520_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(
                    v_expr_509_,
                    v___y_514_,
                    v___y_515_,
                    v___y_516_,
                    v___y_517_,
                    v___y_518_,
                );
                if lean_obj_tag(v___x_520_) == 0 {
                    v_a_521_ = lean_ctor_get(v___x_520_, 0);
                    lean_inc(v_a_521_);
                    lean_dec_ref_known(v___x_520_, 1);
                    v___x_522_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(
                        v_val_510_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_,
                    );
                    if lean_obj_tag(v___x_522_) == 0 {
                        v_a_523_ = lean_ctor_get(v___x_522_, 0);
                        v_isSharedCheck_537_ = (!lean_is_exclusive(v___x_522_)) as u8;
                        if v_isSharedCheck_537_ == 0 {
                            v___x_525_ = v___x_522_;
                            v_isShared_526_ = v_isSharedCheck_537_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_523_);
                            lean_dec(v___x_522_);
                            v___x_525_ = lean_box(0);
                            v_isShared_526_ = v_isSharedCheck_537_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_521_);
                        lean_dec_ref(v_h_513_);
                        lean_dec_ref(v_arg_512_);
                        lean_dec(v___x_511_);
                        v_a_538_ = lean_ctor_get(v___x_522_, 0);
                        v_isSharedCheck_545_ = (!lean_is_exclusive(v___x_522_)) as u8;
                        if v_isSharedCheck_545_ == 0 {
                            v___x_540_ = v___x_522_;
                            v_isShared_541_ = v_isSharedCheck_545_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_538_);
                            lean_dec(v___x_522_);
                            v___x_540_ = lean_box(0);
                            v_isShared_541_ = v_isSharedCheck_545_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_h_513_);
                    lean_dec_ref(v_arg_512_);
                    lean_dec(v___x_511_);
                    lean_dec_ref(v_val_510_);
                    return v___x_520_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_523_) == 0 {
                    lean_inc(v_a_521_);
                    v___x_535_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_521_);
                    v___y_528_ = v___x_535_;
                    state = 2;
                    continue;
                } else {
                    v_val_536_ = lean_ctor_get(v_a_523_, 0);
                    lean_inc(v_val_536_);
                    lean_dec_ref_known(v_a_523_, 1);
                    v___y_528_ = v_val_536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_529_ = lean_box(0);
                v___x_530_ = l_Lean_mkConst(v___x_511_, v___x_529_);
                v___x_531_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(
                    v_a_521_, v_arg_512_, v___x_530_, v___y_528_, v_h_513_,
                );
                if v_isShared_526_ == 0 {
                    lean_ctor_set(v___x_525_, 0, v___x_531_);
                    v___x_533_ = v___x_525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
                    v___x_533_ = v_reuseFailAlloc_534_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_533_;
            }
            4 => {
                if v_isShared_541_ == 0 {
                    v___x_543_ = v___x_540_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
                    v___x_543_ = v_reuseFailAlloc_544_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed(
    mut v_expr_546_: *mut LeanObject,
    mut v_val_547_: *mut LeanObject,
    mut v___x_548_: *mut LeanObject,
    mut v_arg_549_: *mut LeanObject,
    mut v_h_550_: *mut LeanObject,
    mut v___y_551_: *mut LeanObject,
    mut v___y_552_: *mut LeanObject,
    mut v___y_553_: *mut LeanObject,
    mut v___y_554_: *mut LeanObject,
    mut v___y_555_: *mut LeanObject,
    mut v___y_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_557_: *mut LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(
        v_expr_546_,
        v_val_547_,
        v___x_548_,
        v_arg_549_,
        v_h_550_,
        v___y_551_,
        v___y_552_,
        v___y_553_,
        v___y_554_,
        v___y_555_,
    );
    lean_dec(v___y_555_);
    lean_dec_ref(v___y_554_);
    lean_dec(v___y_553_);
    lean_dec_ref(v___y_552_);
    lean_dec(v___y_551_);
    return v_res_557_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(
    mut v_h_568_: *mut LeanObject,
    mut v_a_569_: *mut LeanObject,
    mut v_a_570_: *mut LeanObject,
    mut v_a_571_: *mut LeanObject,
    mut v_a_572_: *mut LeanObject,
    mut v_a_573_: *mut LeanObject,
    mut v_a_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: u8 = 0;
    let mut v_arg_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: u8 = 0;
    let mut v_arg_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: u8 = 0;
    let mut v_arg_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_625_: u8 = 0;
    let mut v_val_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_629_: u8 = 0;
    let mut v_bvExpr_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_640_: u8 = 0;
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_645_: u8 = 0;
    let mut v_a_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_653_: u8 = 0;
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v_a_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_662_: u8 = 0;
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_a_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_671_: u8 = 0;
    let mut v_a_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_574_);
                lean_inc_ref(v_a_573_);
                lean_inc(v_a_572_);
                lean_inc_ref(v_a_571_);
                lean_inc_ref(v_h_568_);
                v___x_576_ = lean_infer_type(v_h_568_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
                if lean_obj_tag(v___x_576_) == 0 {
                    v_a_577_ = lean_ctor_get(v___x_576_, 0);
                    lean_inc(v_a_577_);
                    lean_dec_ref_known(v___x_576_, 1);
                    v___x_578_ =
                        l_Lean_Meta_whnfR(v_a_577_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
                    if lean_obj_tag(v___x_578_) == 0 {
                        v_a_579_ = lean_ctor_get(v___x_578_, 0);
                        lean_inc(v_a_579_);
                        lean_dec_ref_known(v___x_578_, 1);
                        v___x_580_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(v_a_579_, v_a_572_);
                        v_a_581_ = lean_ctor_get(v___x_580_, 0);
                        v_isSharedCheck_663_ = (!lean_is_exclusive(v___x_580_)) as u8;
                        if v_isSharedCheck_663_ == 0 {
                            v___x_583_ = v___x_580_;
                            v_isShared_584_ = v_isSharedCheck_663_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_581_);
                            lean_dec(v___x_580_);
                            v___x_583_ = lean_box(0);
                            v_isShared_584_ = v_isSharedCheck_663_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_h_568_);
                        v_a_664_ = lean_ctor_get(v___x_578_, 0);
                        v_isSharedCheck_671_ = (!lean_is_exclusive(v___x_578_)) as u8;
                        if v_isSharedCheck_671_ == 0 {
                            v___x_666_ = v___x_578_;
                            v_isShared_667_ = v_isSharedCheck_671_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_664_);
                            lean_dec(v___x_578_);
                            v___x_666_ = lean_box(0);
                            v_isShared_667_ = v_isSharedCheck_671_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_h_568_);
                    v_a_672_ = lean_ctor_get(v___x_576_, 0);
                    v_isSharedCheck_679_ = (!lean_is_exclusive(v___x_576_)) as u8;
                    if v_isSharedCheck_679_ == 0 {
                        v___x_674_ = v___x_576_;
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_672_);
                        lean_dec(v___x_576_);
                        v___x_674_ = lean_box(0);
                        v_isShared_675_ = v_isSharedCheck_679_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                v___x_585_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_581_, v_a_572_);
                if lean_obj_tag(v___x_585_) == 0 {
                    v_a_586_ = lean_ctor_get(v___x_585_, 0);
                    v_isSharedCheck_654_ = (!lean_is_exclusive(v___x_585_)) as u8;
                    if v_isSharedCheck_654_ == 0 {
                        v___x_588_ = v___x_585_;
                        v_isShared_589_ = v_isSharedCheck_654_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_586_);
                        lean_dec(v___x_585_);
                        v___x_588_ = lean_box(0);
                        v_isShared_589_ = v_isSharedCheck_654_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_583_);
                    lean_dec_ref(v_h_568_);
                    v_a_655_ = lean_ctor_get(v___x_585_, 0);
                    v_isSharedCheck_662_ = (!lean_is_exclusive(v___x_585_)) as u8;
                    if v_isSharedCheck_662_ == 0 {
                        v___x_657_ = v___x_585_;
                        v_isShared_658_ = v_isSharedCheck_662_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_655_);
                        lean_dec(v___x_585_);
                        v___x_657_ = lean_box(0);
                        v_isShared_658_ = v_isSharedCheck_662_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_595_ = l_Lean_Expr_cleanupAnnotations(v_a_586_);
                v___x_596_ = l_Lean_Expr_isApp(v___x_595_);
                if v___x_596_ == 0 {
                    lean_dec_ref(v___x_595_);
                    lean_del_object(v___x_583_);
                    lean_dec_ref(v_h_568_);
                    state = 3;
                    continue;
                } else {
                    v_arg_597_ = lean_ctor_get(v___x_595_, 1);
                    lean_inc_ref(v_arg_597_);
                    v___x_598_ = l_Lean_Expr_appFnCleanup___redArg(v___x_595_);
                    v___x_599_ = l_Lean_Expr_isApp(v___x_598_);
                    if v___x_599_ == 0 {
                        lean_dec_ref(v___x_598_);
                        lean_dec_ref(v_arg_597_);
                        lean_del_object(v___x_583_);
                        lean_dec_ref(v_h_568_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_600_ = lean_ctor_get(v___x_598_, 1);
                        lean_inc_ref(v_arg_600_);
                        v___x_601_ = l_Lean_Expr_appFnCleanup___redArg(v___x_598_);
                        v___x_602_ = l_Lean_Expr_isApp(v___x_601_);
                        if v___x_602_ == 0 {
                            lean_dec_ref(v___x_601_);
                            lean_dec_ref(v_arg_600_);
                            lean_dec_ref(v_arg_597_);
                            lean_del_object(v___x_583_);
                            lean_dec_ref(v_h_568_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_603_ = lean_ctor_get(v___x_601_, 1);
                            lean_inc_ref(v_arg_603_);
                            v___x_604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_601_);
                            v___x_605_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1;
                            v___x_606_ = l_Lean_Expr_isConstOf(v___x_604_, v___x_605_);
                            lean_dec_ref(v___x_604_);
                            if v___x_606_ == 0 {
                                lean_dec_ref(v_arg_603_);
                                lean_dec_ref(v_arg_600_);
                                lean_dec_ref(v_arg_597_);
                                lean_del_object(v___x_583_);
                                lean_dec_ref(v_h_568_);
                                state = 3;
                                continue;
                            } else {
                                lean_del_object(v___x_588_);
                                v___x_607_ = l_Lean_Expr_cleanupAnnotations(v_arg_603_);
                                v___x_608_ =
                                    l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3;
                                v___x_609_ = l_Lean_Expr_isConstOf(v___x_607_, v___x_608_);
                                lean_dec_ref(v___x_607_);
                                if v___x_609_ == 0 {
                                    lean_dec_ref(v_arg_600_);
                                    lean_dec_ref(v_arg_597_);
                                    lean_dec_ref(v_h_568_);
                                    v___x_610_ = lean_box(0);
                                    if v_isShared_584_ == 0 {
                                        lean_ctor_set(v___x_583_, 0, v___x_610_);
                                        v___x_612_ = v___x_583_;
                                        state = 5;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
                                        v___x_612_ = v_reuseFailAlloc_613_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    v___x_614_ = l_Lean_Expr_cleanupAnnotations(v_arg_597_);
                                    v___x_615_ =
                                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5;
                                    v___x_616_ = l_Lean_Expr_isConstOf(v___x_614_, v___x_615_);
                                    lean_dec_ref(v___x_614_);
                                    if v___x_616_ == 0 {
                                        lean_dec_ref(v_arg_600_);
                                        lean_dec_ref(v_h_568_);
                                        v___x_617_ = lean_box(0);
                                        if v_isShared_584_ == 0 {
                                            lean_ctor_set(v___x_583_, 0, v___x_617_);
                                            v___x_619_ = v___x_583_;
                                            state = 6;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_620_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
                                            v___x_619_ = v_reuseFailAlloc_620_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        lean_del_object(v___x_583_);
                                        lean_inc_ref(v_arg_600_);
                                        v___x_621_ =
                                            l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(
                                                v_arg_600_, v_a_569_, v_a_570_, v_a_571_, v_a_572_,
                                                v_a_573_, v_a_574_,
                                            );
                                        if lean_obj_tag(v___x_621_) == 0 {
                                            v_a_622_ = lean_ctor_get(v___x_621_, 0);
                                            v_isSharedCheck_645_ =
                                                (!lean_is_exclusive(v___x_621_)) as u8;
                                            if v_isSharedCheck_645_ == 0 {
                                                v___x_624_ = v___x_621_;
                                                v_isShared_625_ = v_isSharedCheck_645_;
                                                state = 7;
                                                continue;
                                            } else {
                                                lean_inc(v_a_622_);
                                                lean_dec(v___x_621_);
                                                v___x_624_ = lean_box(0);
                                                v_isShared_625_ = v_isSharedCheck_645_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_arg_600_);
                                            lean_dec_ref(v_h_568_);
                                            v_a_646_ = lean_ctor_get(v___x_621_, 0);
                                            v_isSharedCheck_653_ =
                                                (!lean_is_exclusive(v___x_621_)) as u8;
                                            if v_isSharedCheck_653_ == 0 {
                                                v___x_648_ = v___x_621_;
                                                v_isShared_649_ = v_isSharedCheck_653_;
                                                state = 12;
                                                continue;
                                            } else {
                                                lean_inc(v_a_646_);
                                                lean_dec(v___x_621_);
                                                v___x_648_ = lean_box(0);
                                                v_isShared_649_ = v_isSharedCheck_653_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_591_ = lean_box(0);
                if v_isShared_589_ == 0 {
                    lean_ctor_set(v___x_588_, 0, v___x_591_);
                    v___x_593_ = v___x_588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
                    v___x_593_ = v_reuseFailAlloc_594_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_593_;
            }
            5 => {
                return v___x_612_;
            }
            6 => {
                return v___x_619_;
            }
            7 => {
                if lean_obj_tag(v_a_622_) == 1 {
                    v_val_626_ = lean_ctor_get(v_a_622_, 0);
                    v_isSharedCheck_640_ = (!lean_is_exclusive(v_a_622_)) as u8;
                    if v_isSharedCheck_640_ == 0 {
                        v___x_628_ = v_a_622_;
                        v_isShared_629_ = v_isSharedCheck_640_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_626_);
                        lean_dec(v_a_622_);
                        v___x_628_ = lean_box(0);
                        v_isShared_629_ = v_isSharedCheck_640_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_622_);
                    lean_dec_ref(v_arg_600_);
                    lean_dec_ref(v_h_568_);
                    v___x_641_ = lean_box(0);
                    if v_isShared_625_ == 0 {
                        lean_ctor_set(v___x_624_, 0, v___x_641_);
                        v___x_643_ = v___x_624_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_641_);
                        v___x_643_ = v_reuseFailAlloc_644_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                v_bvExpr_630_ = lean_ctor_get(v_val_626_, 0);
                lean_inc_ref(v_bvExpr_630_);
                v_expr_631_ = lean_ctor_get(v_val_626_, 3);
                lean_inc_ref_n(v_expr_631_, 2);
                v___f_632_ = lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed
                        as *mut core::ffi::c_void,
                    11,
                    5,
                );
                lean_closure_set(v___f_632_, 0, v_expr_631_);
                lean_closure_set(v___f_632_, 1, v_val_626_);
                lean_closure_set(v___f_632_, 2, v___x_615_);
                lean_closure_set(v___f_632_, 3, v_arg_600_);
                lean_closure_set(v___f_632_, 4, v_h_568_);
                v___x_633_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_633_, 0, v_bvExpr_630_);
                lean_ctor_set(v___x_633_, 1, v___f_632_);
                lean_ctor_set(v___x_633_, 2, v_expr_631_);
                if v_isShared_629_ == 0 {
                    lean_ctor_set(v___x_628_, 0, v___x_633_);
                    v___x_635_ = v___x_628_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_633_);
                    v___x_635_ = v_reuseFailAlloc_639_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_625_ == 0 {
                    lean_ctor_set(v___x_624_, 0, v___x_635_);
                    v___x_637_ = v___x_624_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
                    v___x_637_ = v_reuseFailAlloc_638_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_637_;
            }
            11 => {
                return v___x_643_;
            }
            12 => {
                if v_isShared_649_ == 0 {
                    v___x_651_ = v___x_648_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
                    v___x_651_ = v_reuseFailAlloc_652_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_651_;
            }
            14 => {
                if v_isShared_658_ == 0 {
                    v___x_660_ = v___x_657_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
                    v___x_660_ = v_reuseFailAlloc_661_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_660_;
            }
            16 => {
                if v_isShared_667_ == 0 {
                    v___x_669_ = v___x_666_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
                    v___x_669_ = v_reuseFailAlloc_670_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_669_;
            }
            18 => {
                if v_isShared_675_ == 0 {
                    v___x_677_ = v___x_674_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
                    v___x_677_ = v_reuseFailAlloc_678_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(
    mut v_h_680_: *mut LeanObject,
    mut v_a_681_: *mut LeanObject,
    mut v_a_682_: *mut LeanObject,
    mut v_a_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
    mut v_a_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_688_: *mut LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(
        v_h_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_,
    );
    lean_dec(v_a_686_);
    lean_dec_ref(v_a_685_);
    lean_dec(v_a_684_);
    lean_dec_ref(v_a_683_);
    lean_dec(v_a_682_);
    lean_dec(v_a_681_);
    return v_res_688_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6()
-> *mut LeanObject {
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    v___x_700_ = lean_box(0);
    v___x_701_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5;
    v___x_702_ = l_Lean_mkConst(v___x_701_, v___x_700_);
    return v___x_702_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0(
    mut v_satAtAtoms_703_: *mut LeanObject,
    mut v_satAtAtoms_704_: *mut LeanObject,
    mut v_expr_705_: *mut LeanObject,
    mut v_expr_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
    mut v___y_708_: *mut LeanObject,
    mut v___y_709_: *mut LeanObject,
    mut v___y_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_721_: u8 = 0;
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_713_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(
                    v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_,
                );
                if lean_obj_tag(v___x_713_) == 0 {
                    v_a_714_ = lean_ctor_get(v___x_713_, 0);
                    lean_inc(v_a_714_);
                    lean_dec_ref_known(v___x_713_, 1);
                    lean_inc(v___y_711_);
                    lean_inc_ref(v___y_710_);
                    lean_inc(v___y_709_);
                    lean_inc_ref(v___y_708_);
                    lean_inc(v___y_707_);
                    v___x_715_ = lean_apply_6(
                        v_satAtAtoms_703_,
                        v___y_707_,
                        v___y_708_,
                        v___y_709_,
                        v___y_710_,
                        v___y_711_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_715_) == 0 {
                        v_a_716_ = lean_ctor_get(v___x_715_, 0);
                        lean_inc(v_a_716_);
                        lean_dec_ref_known(v___x_715_, 1);
                        lean_inc(v___y_711_);
                        lean_inc_ref(v___y_710_);
                        lean_inc(v___y_709_);
                        lean_inc_ref(v___y_708_);
                        lean_inc(v___y_707_);
                        v___x_717_ = lean_apply_6(
                            v_satAtAtoms_704_,
                            v___y_707_,
                            v___y_708_,
                            v___y_709_,
                            v___y_710_,
                            v___y_711_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_717_) == 0 {
                            v_a_718_ = lean_ctor_get(v___x_717_, 0);
                            v_isSharedCheck_727_ = (!lean_is_exclusive(v___x_717_)) as u8;
                            if v_isSharedCheck_727_ == 0 {
                                v___x_720_ = v___x_717_;
                                v_isShared_721_ = v_isSharedCheck_727_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_718_);
                                lean_dec(v___x_717_);
                                v___x_720_ = lean_box(0);
                                v_isShared_721_ = v_isSharedCheck_727_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_716_);
                            lean_dec(v_a_714_);
                            lean_dec_ref(v_expr_706_);
                            lean_dec_ref(v_expr_705_);
                            return v___x_717_;
                        }
                    } else {
                        lean_dec(v_a_714_);
                        lean_dec_ref(v_expr_706_);
                        lean_dec_ref(v_expr_705_);
                        lean_dec_ref(v_satAtAtoms_704_);
                        return v___x_715_;
                    }
                } else {
                    lean_dec_ref(v_expr_706_);
                    lean_dec_ref(v_expr_705_);
                    lean_dec_ref(v_satAtAtoms_704_);
                    lean_dec_ref(v_satAtAtoms_703_);
                    return v___x_713_;
                }
            }
            1 => {
                v___x_722_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6,
                );
                v___x_723_ = l_Lean_mkApp5(
                    v___x_722_,
                    v_expr_705_,
                    v_expr_706_,
                    v_a_714_,
                    v_a_716_,
                    v_a_718_,
                );
                if v_isShared_721_ == 0 {
                    lean_ctor_set(v___x_720_, 0, v___x_723_);
                    v___x_725_ = v___x_720_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
                    v___x_725_ = v_reuseFailAlloc_726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_725_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___boxed(
    mut v_satAtAtoms_728_: *mut LeanObject,
    mut v_satAtAtoms_729_: *mut LeanObject,
    mut v_expr_730_: *mut LeanObject,
    mut v_expr_731_: *mut LeanObject,
    mut v___y_732_: *mut LeanObject,
    mut v___y_733_: *mut LeanObject,
    mut v___y_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
    mut v___y_736_: *mut LeanObject,
    mut v___y_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_738_: *mut LeanObject = core::ptr::null_mut();
    v_res_738_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0(
        v_satAtAtoms_728_,
        v_satAtAtoms_729_,
        v_expr_730_,
        v_expr_731_,
        v___y_732_,
        v___y_733_,
        v___y_734_,
        v___y_735_,
        v___y_736_,
    );
    lean_dec(v___y_736_);
    lean_dec_ref(v___y_735_);
    lean_dec(v___y_734_);
    lean_dec_ref(v___y_733_);
    lean_dec(v___y_732_);
    return v_res_738_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3() -> *mut LeanObject
{
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = lean_box(0);
    v___x_748_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2;
    v___x_749_ = l_Lean_mkConst(v___x_748_, v___x_747_);
    return v___x_749_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6() -> *mut LeanObject
{
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    v___x_756_ = lean_box(0);
    v___x_757_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5;
    v___x_758_ = l_Lean_mkConst(v___x_757_, v___x_756_);
    return v___x_758_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10() -> *mut LeanObject
{
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    v___x_767_ = lean_box(0);
    v___x_768_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9;
    v___x_769_ = l_Lean_mkConst(v___x_768_, v___x_767_);
    return v___x_769_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(
    mut v_x_770_: *mut LeanObject,
    mut v_y_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bvExpr_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_satAtAtoms_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bvExpr_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_satAtAtoms_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_781_: u8 = 0;
    let mut v___f_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_bvExpr_772_ = lean_ctor_get(v_x_770_, 0);
                lean_inc_ref(v_bvExpr_772_);
                v_satAtAtoms_773_ = lean_ctor_get(v_x_770_, 1);
                lean_inc_ref(v_satAtAtoms_773_);
                v_expr_774_ = lean_ctor_get(v_x_770_, 2);
                lean_inc_ref(v_expr_774_);
                lean_dec_ref(v_x_770_);
                v_bvExpr_775_ = lean_ctor_get(v_y_771_, 0);
                v_satAtAtoms_776_ = lean_ctor_get(v_y_771_, 1);
                v_expr_777_ = lean_ctor_get(v_y_771_, 2);
                v_isSharedCheck_791_ = (!lean_is_exclusive(v_y_771_)) as u8;
                if v_isSharedCheck_791_ == 0 {
                    v___x_779_ = v_y_771_;
                    v_isShared_780_ = v_isSharedCheck_791_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_expr_777_);
                    lean_inc(v_satAtAtoms_776_);
                    lean_inc(v_bvExpr_775_);
                    lean_dec(v_y_771_);
                    v___x_779_ = lean_box(0);
                    v_isShared_780_ = v_isSharedCheck_791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_781_ = 0;
                lean_inc_ref(v_expr_777_);
                lean_inc_ref(v_expr_774_);
                v___f_782_ = lean_alloc_closure(
                    l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___boxed
                        as *mut core::ffi::c_void,
                    10,
                    4,
                );
                lean_closure_set(v___f_782_, 0, v_satAtAtoms_773_);
                lean_closure_set(v___f_782_, 1, v_satAtAtoms_776_);
                lean_closure_set(v___f_782_, 2, v_expr_774_);
                lean_closure_set(v___f_782_, 3, v_expr_777_);
                v___x_783_ = lean_alloc_ctor(3, 2, (1) as u32);
                lean_ctor_set(v___x_783_, 0, v_bvExpr_772_);
                lean_ctor_set(v___x_783_, 1, v_bvExpr_775_);
                lean_ctor_set_uint8(
                    v___x_783_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_781_,
                );
                v___x_784_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3,
                );
                v___x_785_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6,
                );
                v___x_786_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10,
                );
                v___x_787_ =
                    l_Lean_mkApp4(v___x_784_, v___x_785_, v___x_786_, v_expr_774_, v_expr_777_);
                if v_isShared_780_ == 0 {
                    lean_ctor_set(v___x_779_, 2, v___x_787_);
                    lean_ctor_set(v___x_779_, 1, v___f_782_);
                    lean_ctor_set(v___x_779_, 0, v___x_783_);
                    v___x_789_ = v___x_779_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_783_);
                    lean_ctor_set(v_reuseFailAlloc_790_, 1, v___f_782_);
                    lean_ctor_set(v_reuseFailAlloc_790_, 2, v___x_787_);
                    v___x_789_ = v_reuseFailAlloc_790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(
    mut v_msgData_792_: *mut LeanObject,
    mut v___y_793_: *mut LeanObject,
    mut v___y_794_: *mut LeanObject,
    mut v___y_795_: *mut LeanObject,
    mut v___y_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = lean_st_ref_get(v___y_796_);
    v_env_799_ = lean_ctor_get(v___x_798_, 0);
    lean_inc_ref(v_env_799_);
    lean_dec(v___x_798_);
    v___x_800_ = lean_st_ref_get(v___y_794_);
    v_mctx_801_ = lean_ctor_get(v___x_800_, 0);
    lean_inc_ref(v_mctx_801_);
    lean_dec(v___x_800_);
    v_lctx_802_ = lean_ctor_get(v___y_793_, 2);
    v_options_803_ = lean_ctor_get(v___y_795_, 2);
    lean_inc_ref(v_options_803_);
    lean_inc_ref(v_lctx_802_);
    v___x_804_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_804_, 0, v_env_799_);
    lean_ctor_set(v___x_804_, 1, v_mctx_801_);
    lean_ctor_set(v___x_804_, 2, v_lctx_802_);
    lean_ctor_set(v___x_804_, 3, v_options_803_);
    v___x_805_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_805_, 0, v___x_804_);
    lean_ctor_set(v___x_805_, 1, v_msgData_792_);
    v___x_806_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_806_, 0, v___x_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(
    mut v_msgData_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
    mut v___y_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_813_: *mut LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msgData_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
    lean_dec(v___y_811_);
    lean_dec_ref(v___y_810_);
    lean_dec(v___y_809_);
    lean_dec_ref(v___y_808_);
    return v_res_813_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(
    mut v_msg_814_: *mut LeanObject,
    mut v___y_815_: *mut LeanObject,
    mut v___y_816_: *mut LeanObject,
    mut v___y_817_: *mut LeanObject,
    mut v___y_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_825_: u8 = 0;
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_820_ = lean_ctor_get(v___y_817_, 5);
                v___x_821_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msg_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
                v_a_822_ = lean_ctor_get(v___x_821_, 0);
                v_isSharedCheck_830_ = (!lean_is_exclusive(v___x_821_)) as u8;
                if v_isSharedCheck_830_ == 0 {
                    v___x_824_ = v___x_821_;
                    v_isShared_825_ = v_isSharedCheck_830_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_822_);
                    lean_dec(v___x_821_);
                    v___x_824_ = lean_box(0);
                    v_isShared_825_ = v_isSharedCheck_830_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_820_);
                v___x_826_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_826_, 0, v_ref_820_);
                lean_ctor_set(v___x_826_, 1, v_a_822_);
                if v_isShared_825_ == 0 {
                    lean_ctor_set_tag(v___x_824_, 1);
                    lean_ctor_set(v___x_824_, 0, v___x_826_);
                    v___x_828_ = v___x_824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
                    v___x_828_ = v_reuseFailAlloc_829_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(
    mut v_msg_831_: *mut LeanObject,
    mut v___y_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
    mut v___y_835_: *mut LeanObject,
    mut v___y_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_837_: *mut LeanObject = core::ptr::null_mut();
    v_res_837_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
    lean_dec(v___y_835_);
    lean_dec_ref(v___y_834_);
    lean_dec(v___y_833_);
    lean_dec_ref(v___y_832_);
    return v_res_837_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2()
-> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    v___x_845_ = lean_box(0);
    v___x_846_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1;
    v___x_847_ = l_Lean_mkConst(v___x_846_, v___x_845_);
    return v___x_847_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6()
-> *mut LeanObject {
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v___x_857_ = lean_box(0);
    v___x_858_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5;
    v___x_859_ = l_Lean_mkConst(v___x_858_, v___x_857_);
    return v___x_859_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8()
-> *mut LeanObject {
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    v___x_861_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7;
    v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
    return v___x_862_;
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(
    mut v_x_863_: *mut LeanObject,
    mut v_h_864_: *mut LeanObject,
    mut v_a_865_: *mut LeanObject,
    mut v_a_866_: *mut LeanObject,
    mut v_a_867_: *mut LeanObject,
    mut v_a_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_atoms_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_satAtAtoms_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_884_: u8 = 0;
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_871_ = lean_st_ref_get(v_a_865_);
                v_atoms_872_ = lean_ctor_get(v___x_871_, 0);
                lean_inc_ref(v_atoms_872_);
                lean_dec(v___x_871_);
                v_size_873_ = lean_ctor_get(v_atoms_872_, 0);
                lean_inc(v_size_873_);
                lean_dec_ref(v_atoms_872_);
                v___x_874_ = lean_unsigned_to_nat(0);
                v___x_875_ = lean_nat_dec_eq(v_size_873_, v___x_874_);
                lean_dec(v_size_873_);
                if v___x_875_ == 0 {
                    v___x_876_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(
                        v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_,
                    );
                    if lean_obj_tag(v___x_876_) == 0 {
                        v_a_877_ = lean_ctor_get(v___x_876_, 0);
                        lean_inc(v_a_877_);
                        lean_dec_ref_known(v___x_876_, 1);
                        v_satAtAtoms_878_ = lean_ctor_get(v_x_863_, 1);
                        lean_inc_ref(v_satAtAtoms_878_);
                        v_expr_879_ = lean_ctor_get(v_x_863_, 2);
                        lean_inc_ref(v_expr_879_);
                        lean_dec_ref(v_x_863_);
                        lean_inc(v_a_869_);
                        lean_inc_ref(v_a_868_);
                        lean_inc(v_a_867_);
                        lean_inc_ref(v_a_866_);
                        lean_inc(v_a_865_);
                        v___x_880_ = lean_apply_6(
                            v_satAtAtoms_878_,
                            v_a_865_,
                            v_a_866_,
                            v_a_867_,
                            v_a_868_,
                            v_a_869_,
                            lean_box(0),
                        );
                        if lean_obj_tag(v___x_880_) == 0 {
                            v_a_881_ = lean_ctor_get(v___x_880_, 0);
                            v_isSharedCheck_893_ = (!lean_is_exclusive(v___x_880_)) as u8;
                            if v_isSharedCheck_893_ == 0 {
                                v___x_883_ = v___x_880_;
                                v_isShared_884_ = v_isSharedCheck_893_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_881_);
                                lean_dec(v___x_880_);
                                v___x_883_ = lean_box(0);
                                v_isShared_884_ = v_isSharedCheck_893_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_expr_879_);
                            lean_dec(v_a_877_);
                            lean_dec_ref(v_h_864_);
                            return v___x_880_;
                        }
                    } else {
                        lean_dec_ref(v_h_864_);
                        lean_dec_ref(v_x_863_);
                        return v___x_876_;
                    }
                } else {
                    lean_dec_ref(v_h_864_);
                    lean_dec_ref(v_x_863_);
                    v___x_894_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8_once
                        ),
                        _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8,
                    );
                    v___x_895_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v___x_894_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
                    return v___x_895_;
                }
            }
            1 => {
                v___x_885_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2,
                );
                lean_inc(v_a_877_);
                v___x_886_ = l_Lean_mkAppB(v___x_885_, v_a_877_, v_expr_879_);
                v___x_887_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6,
                );
                v___x_888_ = l_Lean_Expr_app___override(v_h_864_, v_a_877_);
                v___x_889_ = l_Lean_mkApp3(v___x_887_, v___x_886_, v_a_881_, v___x_888_);
                if v_isShared_884_ == 0 {
                    lean_ctor_set(v___x_883_, 0, v___x_889_);
                    v___x_891_ = v___x_883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
                    v___x_891_ = v_reuseFailAlloc_892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_891_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(
    mut v_x_896_: *mut LeanObject,
    mut v_h_897_: *mut LeanObject,
    mut v_a_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_904_: *mut LeanObject = core::ptr::null_mut();
    v_res_904_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(
        v_x_896_, v_h_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_,
    );
    lean_dec(v_a_902_);
    lean_dec_ref(v_a_901_);
    lean_dec(v_a_900_);
    lean_dec_ref(v_a_899_);
    lean_dec(v_a_898_);
    return v_res_904_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(
    mut v_00_u03b1_905_: *mut LeanObject,
    mut v_msg_906_: *mut LeanObject,
    mut v___y_907_: *mut LeanObject,
    mut v___y_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
    mut v___y_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_906_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
    return v___x_913_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___boxed(
    mut v_00_u03b1_914_: *mut LeanObject,
    mut v_msg_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
    mut v___y_918_: *mut LeanObject,
    mut v___y_919_: *mut LeanObject,
    mut v___y_920_: *mut LeanObject,
    mut v___y_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_922_: *mut LeanObject = core::ptr::null_mut();
    v_res_922_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(
            v_00_u03b1_914_,
            v_msg_915_,
            v___y_916_,
            v___y_917_,
            v___y_918_,
            v___y_919_,
            v___y_920_,
        );
    lean_dec(v___y_920_);
    lean_dec_ref(v___y_919_);
    lean_dec(v___y_918_);
    lean_dec_ref(v___y_917_);
    lean_dec(v___y_916_);
    return v_res_922_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(
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
pub unsafe fn initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
}
