// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.ToExpr
// Imports: Init.Grind.AC Lean.ToExpr
use crate::r#gen::Init::Grind::AC::{initialize_Init_Grind_AC, runtime_initialize_Init_Grind_AC};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::ToExpr::{initialize_Lean_ToExpr, runtime_initialize_Lean_ToExpr};
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__1_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [65, 67, 0],
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__3_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [83, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__4_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [118, 97, 114, 0],
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__2_value)
                as *mut leanh::LeanObject,
            7037901503065350583 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__3_value)
                as *mut leanh::LeanObject,
            15233984863453104988 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__5_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__4_value)
                as *mut leanh::LeanObject,
            13117405551196643749 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__7_value: leanh::LeanStringObject<5> =
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
        m_data: [99, 111, 110, 115, 0],
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_0: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__2_value)
                as *mut leanh::LeanObject,
            7037901503065350583 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__3_value)
                as *mut leanh::LeanObject,
            15233984863453104988 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_AC_ofSeq___closed__8_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__8_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__7_value)
                as *mut leanh::LeanObject,
            7948251239744257903 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_ofSeq___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_instToExprSeq___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_AC_ofSeq as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_AC_instToExprSeq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__2_value)
                as *mut leanh::LeanObject,
            7037901503065350583 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__3_value)
                as *mut leanh::LeanObject,
            15233984863453104988 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_instToExprSeq___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_instToExprSeq___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instToExprSeq___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instToExprSeq___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instToExprSeq___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instToExprSeq: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_ofExpr___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [69, 120, 112, 114, 0],
    };
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__2_value)
                as *mut leanh::LeanObject,
            7037901503065350583 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__0_value)
                as *mut leanh::LeanObject,
            3365831499116467609 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_AC_ofExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__1_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__4_value)
                as *mut leanh::LeanObject,
            18400758817693806756 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_ofExpr___closed__3_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [111, 112, 0],
    };
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__1_value)
                as *mut leanh::LeanObject,
            13563742693681136756 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__2_value)
                as *mut leanh::LeanObject,
            7037901503065350583 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_3: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__0_value)
                as *mut leanh::LeanObject,
            3365831499116467609 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_AC_ofExpr___closed__4_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__4_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__3_value)
                as *mut leanh::LeanObject,
            1076665712378031456 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_ofExpr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_instToExprExpr___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_AC_ofExpr as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_AC_instToExprExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value_aux_1: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__1_value)
            as *mut leanh::LeanObject,
        13563742693681136756 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value_aux_2: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofSeq___closed__2_value)
            as *mut leanh::LeanObject,
        7037901503065350583 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_ofExpr___closed__0_value)
                as *mut leanh::LeanObject,
            3365831499116467609 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_instToExprExpr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_instToExprExpr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instToExprExpr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_AC_instToExprExpr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_instToExprExpr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_AC_instToExprExpr: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_AC_ofSeq___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_104_ = leanh::lean_box(0);
    v___x_105_ = l_Lean_Meta_Grind_AC_ofSeq___closed__5;
    v___x_106_ = l_Lean_mkConst(v___x_105_, v___x_104_);
    return v___x_106_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_ofSeq___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_114_ = leanh::lean_box(0);
    v___x_115_ = l_Lean_Meta_Grind_AC_ofSeq___closed__8;
    v___x_116_ = l_Lean_mkConst(v___x_115_, v___x_114_);
    return v___x_116_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ofSeq(
    mut v_m_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_m_117_) == 0 {
        let mut v_x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_118_ = leanh::lean_ctor_get(v_m_117_, 0);
        leanh::lean_inc(v_x_118_);
        leanh::lean_dec_ref_known(v_m_117_, 1);
        v___x_119_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofSeq___closed__6),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofSeq___closed__6_once),
            _init_l_Lean_Meta_Grind_AC_ofSeq___closed__6,
        );
        v___x_120_ = l_Lean_mkNatLit(v_x_118_);
        v___x_121_ = l_Lean_Expr_app___override(v___x_119_, v___x_120_);
        return v___x_121_;
    } else {
        let mut v_x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_s_123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_122_ = leanh::lean_ctor_get(v_m_117_, 0);
        leanh::lean_inc(v_x_122_);
        v_s_123_ = leanh::lean_ctor_get(v_m_117_, 1);
        leanh::lean_inc_ref(v_s_123_);
        leanh::lean_dec_ref_known(v_m_117_, 2);
        v___x_124_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofSeq___closed__9),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofSeq___closed__9_once),
            _init_l_Lean_Meta_Grind_AC_ofSeq___closed__9,
        );
        v___x_125_ = l_Lean_mkNatLit(v_x_122_);
        v___x_126_ = l_Lean_Meta_Grind_AC_ofSeq(v_s_123_);
        v___x_127_ = l_Lean_mkAppB(v___x_124_, v___x_125_, v___x_126_);
        return v___x_127_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = leanh::lean_box(0);
    v___x_135_ = l_Lean_Meta_Grind_AC_instToExprSeq___closed__1;
    v___x_136_ = l_Lean_mkConst(v___x_135_, v___x_134_);
    return v___x_136_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_137_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__2,
    );
    v___x_138_ = l_Lean_Meta_Grind_AC_instToExprSeq___closed__0;
    v___x_139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_139_, 0, v___x_138_);
    leanh::lean_ctor_set(v___x_139_, 1, v___x_137_);
    return v___x_139_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instToExprSeq() -> *mut leanh::LeanObject {
    let mut v___x_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprSeq___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instToExprSeq___closed__3,
    );
    return v___x_140_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_ofExpr___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_148_ = leanh::lean_box(0);
    v___x_149_ = l_Lean_Meta_Grind_AC_ofExpr___closed__1;
    v___x_150_ = l_Lean_mkConst(v___x_149_, v___x_148_);
    return v___x_150_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_ofExpr___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_158_ = leanh::lean_box(0);
    v___x_159_ = l_Lean_Meta_Grind_AC_ofExpr___closed__4;
    v___x_160_ = l_Lean_mkConst(v___x_159_, v___x_158_);
    return v___x_160_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_ofExpr(
    mut v_m_161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_m_161_) == 0 {
        let mut v_x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_162_ = leanh::lean_ctor_get(v_m_161_, 0);
        leanh::lean_inc(v_x_162_);
        leanh::lean_dec_ref_known(v_m_161_, 1);
        v___x_163_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofExpr___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofExpr___closed__2_once),
            _init_l_Lean_Meta_Grind_AC_ofExpr___closed__2,
        );
        v___x_164_ = l_Lean_mkNatLit(v_x_162_);
        v___x_165_ = l_Lean_Expr_app___override(v___x_163_, v___x_164_);
        return v___x_165_;
    } else {
        let mut v_lhs_166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lhs_166_ = leanh::lean_ctor_get(v_m_161_, 0);
        leanh::lean_inc_ref(v_lhs_166_);
        v_rhs_167_ = leanh::lean_ctor_get(v_m_161_, 1);
        leanh::lean_inc_ref(v_rhs_167_);
        leanh::lean_dec_ref_known(v_m_161_, 2);
        v___x_168_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofExpr___closed__5),
            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_ofExpr___closed__5_once),
            _init_l_Lean_Meta_Grind_AC_ofExpr___closed__5,
        );
        v___x_169_ = l_Lean_Meta_Grind_AC_ofExpr(v_lhs_166_);
        v___x_170_ = l_Lean_Meta_Grind_AC_ofExpr(v_rhs_167_);
        v___x_171_ = l_Lean_mkAppB(v___x_168_, v___x_169_, v___x_170_);
        return v___x_171_;
    }
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_178_ = leanh::lean_box(0);
    v___x_179_ = l_Lean_Meta_Grind_AC_instToExprExpr___closed__1;
    v___x_180_ = l_Lean_mkConst(v___x_179_, v___x_178_);
    return v___x_180_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_181_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__2_once),
        _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__2,
    );
    v___x_182_ = l_Lean_Meta_Grind_AC_instToExprExpr___closed__0;
    v___x_183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_183_, 0, v___x_182_);
    leanh::lean_ctor_set(v___x_183_, 1, v___x_181_);
    return v___x_183_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_instToExprExpr() -> *mut leanh::LeanObject {
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_instToExprExpr___closed__3_once),
        _init_l_Lean_Meta_Grind_AC_instToExprExpr___closed__3,
    );
    return v___x_184_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_AC_instToExprSeq = _init_l_Lean_Meta_Grind_AC_instToExprSeq();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprSeq);
    l_Lean_Meta_Grind_AC_instToExprExpr = _init_l_Lean_Meta_Grind_AC_instToExprExpr();
    leanh::lean_mark_persistent(l_Lean_Meta_Grind_AC_instToExprExpr);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_ToExpr(builtin);
}