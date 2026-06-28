// Lean compiler output
// Module: Lean.Meta.IntInstTesters
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_Int_mkInstAdd, l_Lean_Int_mkInstHAdd, l_Lean_Int_mkInstHMul,
    l_Lean_Int_mkInstHSub, l_Lean_Int_mkInstLE, l_Lean_Int_mkInstLT, l_Lean_Int_mkInstMul,
    l_Lean_Int_mkInstNeg, l_Lean_Int_mkInstSub, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_isDefEqI, runtime_initialize_Lean_Meta_Basic,
};
pub static l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10588691866721272861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value:
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
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        6362876895233142233 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12954774014962000782 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13651631092972606748 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8729007094553737573 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        870450877493123738 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstModInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 77, 111, 100, 0],
};
static mut l_Lean_Meta_Structural_isInstModInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstModInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstModInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13229674978604159643 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstModInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 68, 118, 100, 0],
};
static mut l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8672774792852739236 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9594062259507646949 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10135981711945425184 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        18134279130838690737 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 68, 105, 118, 0],
};
static mut l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1334142589224437282 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 77, 111, 100, 0],
};
static mut l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        6326466896415492082 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 76, 84, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9121383836933346478 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0_value:
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
    m_data: [105, 110, 115, 116, 76, 69, 73, 110, 116, 0],
};
static mut l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17428246012942847934 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 115, 116, 78, 97, 116, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7262162576643354395 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 110, 115, 116, 80, 111, 119, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        290288684272968877 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [105, 110, 115, 116, 72, 80, 111, 119, 0],
};
static mut l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14410956716278334933 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_DefEq_isInstDvdInt___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_DefEq_isInstDvdInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatInt___redArg(
    mut v_e_1072_: *mut crate::leanh::LeanObject,
    mut v_a_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1081_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1093_: u8 = 0;
    let mut v_a_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1075_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1072_, v_a_1073_);
                if crate::leanh::lean_obj_tag(v___x_1075_) == 0 {
                    v_a_1076_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                    v_isSharedCheck_1093_ = (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                    if v_isSharedCheck_1093_ == 0 {
                        v___x_1078_ = v___x_1075_;
                        v_isShared_1079_ = v_isSharedCheck_1093_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1076_);
                        crate::leanh::lean_dec(v___x_1075_);
                        v___x_1078_ = crate::leanh::lean_box(0);
                        v_isShared_1079_ = v_isSharedCheck_1093_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1094_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                    v_isSharedCheck_1101_ = (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                    if v_isSharedCheck_1101_ == 0 {
                        v___x_1096_ = v___x_1075_;
                        v_isShared_1097_ = v_isSharedCheck_1101_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1094_);
                        crate::leanh::lean_dec(v___x_1075_);
                        v___x_1096_ = crate::leanh::lean_box(0);
                        v_isShared_1097_ = v_isSharedCheck_1101_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1086_ = l_Lean_Expr_cleanupAnnotations(v_a_1076_);
                v___x_1087_ = l_Lean_Expr_isApp(v___x_1086_);
                if v___x_1087_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1086_);
                    state = 2;
                    continue;
                } else {
                    v___x_1088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1086_);
                    v___x_1089_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1;
                    v___x_1090_ = l_Lean_Expr_isConstOf(v___x_1088_, v___x_1089_);
                    crate::leanh::lean_dec_ref(v___x_1088_);
                    if v___x_1090_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_1078_);
                        v___x_1091_ = crate::leanh::lean_box((v___x_1090_) as usize);
                        v___x_1092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1092_, 0, v___x_1091_);
                        return v___x_1092_;
                    }
                }
            }
            2 => {
                v___x_1081_ = 0;
                v___x_1082_ = crate::leanh::lean_box((v___x_1081_) as usize);
                if v_isShared_1079_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1078_, 0, v___x_1082_);
                    v___x_1084_ = v___x_1078_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
                    v___x_1084_ = v_reuseFailAlloc_1085_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1084_;
            }
            4 => {
                if v_isShared_1097_ == 0 {
                    v___x_1099_ = v___x_1096_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
                    v___x_1099_ = v_reuseFailAlloc_1100_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatInt___redArg___boxed(
    mut v_e_1102_: *mut crate::leanh::LeanObject,
    mut v_a_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1105_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v_e_1102_, v_a_1103_);
    crate::leanh::lean_dec(v_a_1103_);
    return v_res_1105_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatInt(
    mut v_e_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1112_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v_e_1106_, v_a_1108_);
    return v___x_1112_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatInt___boxed(
    mut v_e_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
    mut v_a_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1119_ = l_Lean_Meta_Structural_isInstOfNatInt(
        v_e_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_,
    );
    crate::leanh::lean_dec(v_a_1117_);
    crate::leanh::lean_dec_ref(v_a_1116_);
    crate::leanh::lean_dec(v_a_1115_);
    crate::leanh::lean_dec_ref(v_a_1114_);
    return v_res_1119_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNegInt___redArg(
    mut v_e_1125_: *mut crate::leanh::LeanObject,
    mut v_a_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: u8 = 0;
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1140_: u8 = 0;
    let mut v_a_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1144_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1128_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1125_, v_a_1126_);
                if crate::leanh::lean_obj_tag(v___x_1128_) == 0 {
                    v_a_1129_ = crate::leanh::lean_ctor_get(v___x_1128_, 0);
                    v_isSharedCheck_1140_ = (!crate::leanh::lean_is_exclusive(v___x_1128_)) as u8;
                    if v_isSharedCheck_1140_ == 0 {
                        v___x_1131_ = v___x_1128_;
                        v_isShared_1132_ = v_isSharedCheck_1140_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1129_);
                        crate::leanh::lean_dec(v___x_1128_);
                        v___x_1131_ = crate::leanh::lean_box(0);
                        v_isShared_1132_ = v_isSharedCheck_1140_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1141_ = crate::leanh::lean_ctor_get(v___x_1128_, 0);
                    v_isSharedCheck_1148_ = (!crate::leanh::lean_is_exclusive(v___x_1128_)) as u8;
                    if v_isSharedCheck_1148_ == 0 {
                        v___x_1143_ = v___x_1128_;
                        v_isShared_1144_ = v_isSharedCheck_1148_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1141_);
                        crate::leanh::lean_dec(v___x_1128_);
                        v___x_1143_ = crate::leanh::lean_box(0);
                        v_isShared_1144_ = v_isSharedCheck_1148_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1133_ = l_Lean_Expr_cleanupAnnotations(v_a_1129_);
                v___x_1134_ = l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2;
                v___x_1135_ = l_Lean_Expr_isConstOf(v___x_1133_, v___x_1134_);
                crate::leanh::lean_dec_ref(v___x_1133_);
                v___x_1136_ = crate::leanh::lean_box((v___x_1135_) as usize);
                if v_isShared_1132_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1131_, 0, v___x_1136_);
                    v___x_1138_ = v___x_1131_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
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
                    v_reuseFailAlloc_1147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
                    v___x_1146_ = v_reuseFailAlloc_1147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstNegInt___redArg___boxed(
    mut v_e_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1152_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_1149_, v_a_1150_);
    crate::leanh::lean_dec(v_a_1150_);
    return v_res_1152_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNegInt(
    mut v_e_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
    mut v_a_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_1153_, v_a_1155_);
    return v___x_1159_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNegInt___boxed(
    mut v_e_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
    mut v_a_1162_: *mut crate::leanh::LeanObject,
    mut v_a_1163_: *mut crate::leanh::LeanObject,
    mut v_a_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ =
        l_Lean_Meta_Structural_isInstNegInt(v_e_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
    crate::leanh::lean_dec(v_a_1164_);
    crate::leanh::lean_dec_ref(v_a_1163_);
    crate::leanh::lean_dec(v_a_1162_);
    crate::leanh::lean_dec_ref(v_a_1161_);
    return v_res_1166_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddInt___redArg(
    mut v_e_1171_: *mut crate::leanh::LeanObject,
    mut v_a_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1178_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: u8 = 0;
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut v_a_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1190_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1174_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1171_, v_a_1172_);
                if crate::leanh::lean_obj_tag(v___x_1174_) == 0 {
                    v_a_1175_ = crate::leanh::lean_ctor_get(v___x_1174_, 0);
                    v_isSharedCheck_1186_ = (!crate::leanh::lean_is_exclusive(v___x_1174_)) as u8;
                    if v_isSharedCheck_1186_ == 0 {
                        v___x_1177_ = v___x_1174_;
                        v_isShared_1178_ = v_isSharedCheck_1186_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1175_);
                        crate::leanh::lean_dec(v___x_1174_);
                        v___x_1177_ = crate::leanh::lean_box(0);
                        v_isShared_1178_ = v_isSharedCheck_1186_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1187_ = crate::leanh::lean_ctor_get(v___x_1174_, 0);
                    v_isSharedCheck_1194_ = (!crate::leanh::lean_is_exclusive(v___x_1174_)) as u8;
                    if v_isSharedCheck_1194_ == 0 {
                        v___x_1189_ = v___x_1174_;
                        v_isShared_1190_ = v_isSharedCheck_1194_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1187_);
                        crate::leanh::lean_dec(v___x_1174_);
                        v___x_1189_ = crate::leanh::lean_box(0);
                        v_isShared_1190_ = v_isSharedCheck_1194_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1179_ = l_Lean_Expr_cleanupAnnotations(v_a_1175_);
                v___x_1180_ = l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1;
                v___x_1181_ = l_Lean_Expr_isConstOf(v___x_1179_, v___x_1180_);
                crate::leanh::lean_dec_ref(v___x_1179_);
                v___x_1182_ = crate::leanh::lean_box((v___x_1181_) as usize);
                if v_isShared_1178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1177_, 0, v___x_1182_);
                    v___x_1184_ = v___x_1177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
                    v___x_1184_ = v_reuseFailAlloc_1185_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1184_;
            }
            3 => {
                if v_isShared_1190_ == 0 {
                    v___x_1192_ = v___x_1189_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
                    v___x_1192_ = v_reuseFailAlloc_1193_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddInt___redArg___boxed(
    mut v_e_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_1195_, v_a_1196_);
    crate::leanh::lean_dec(v_a_1196_);
    return v_res_1198_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddInt(
    mut v_e_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
    mut v_a_1201_: *mut crate::leanh::LeanObject,
    mut v_a_1202_: *mut crate::leanh::LeanObject,
    mut v_a_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_1199_, v_a_1201_);
    return v___x_1205_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddInt___boxed(
    mut v_e_1206_: *mut crate::leanh::LeanObject,
    mut v_a_1207_: *mut crate::leanh::LeanObject,
    mut v_a_1208_: *mut crate::leanh::LeanObject,
    mut v_a_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
    mut v_a_1211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1212_ =
        l_Lean_Meta_Structural_isInstAddInt(v_e_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_);
    crate::leanh::lean_dec(v_a_1210_);
    crate::leanh::lean_dec_ref(v_a_1209_);
    crate::leanh::lean_dec(v_a_1208_);
    crate::leanh::lean_dec_ref(v_a_1207_);
    return v_res_1212_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubInt___redArg(
    mut v_e_1217_: *mut crate::leanh::LeanObject,
    mut v_a_1218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1224_: u8 = 0;
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1232_: u8 = 0;
    let mut v_a_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1220_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1217_, v_a_1218_);
                if crate::leanh::lean_obj_tag(v___x_1220_) == 0 {
                    v_a_1221_ = crate::leanh::lean_ctor_get(v___x_1220_, 0);
                    v_isSharedCheck_1232_ = (!crate::leanh::lean_is_exclusive(v___x_1220_)) as u8;
                    if v_isSharedCheck_1232_ == 0 {
                        v___x_1223_ = v___x_1220_;
                        v_isShared_1224_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1221_);
                        crate::leanh::lean_dec(v___x_1220_);
                        v___x_1223_ = crate::leanh::lean_box(0);
                        v_isShared_1224_ = v_isSharedCheck_1232_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1233_ = crate::leanh::lean_ctor_get(v___x_1220_, 0);
                    v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v___x_1220_)) as u8;
                    if v_isSharedCheck_1240_ == 0 {
                        v___x_1235_ = v___x_1220_;
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1233_);
                        crate::leanh::lean_dec(v___x_1220_);
                        v___x_1235_ = crate::leanh::lean_box(0);
                        v_isShared_1236_ = v_isSharedCheck_1240_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1225_ = l_Lean_Expr_cleanupAnnotations(v_a_1221_);
                v___x_1226_ = l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1;
                v___x_1227_ = l_Lean_Expr_isConstOf(v___x_1225_, v___x_1226_);
                crate::leanh::lean_dec_ref(v___x_1225_);
                v___x_1228_ = crate::leanh::lean_box((v___x_1227_) as usize);
                if v_isShared_1224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1223_, 0, v___x_1228_);
                    v___x_1230_ = v___x_1223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1231_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
                    v___x_1230_ = v_reuseFailAlloc_1231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1230_;
            }
            3 => {
                if v_isShared_1236_ == 0 {
                    v___x_1238_ = v___x_1235_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1239_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
                    v___x_1238_ = v_reuseFailAlloc_1239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubInt___redArg___boxed(
    mut v_e_1241_: *mut crate::leanh::LeanObject,
    mut v_a_1242_: *mut crate::leanh::LeanObject,
    mut v_a_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_1241_, v_a_1242_);
    crate::leanh::lean_dec(v_a_1242_);
    return v_res_1244_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubInt(
    mut v_e_1245_: *mut crate::leanh::LeanObject,
    mut v_a_1246_: *mut crate::leanh::LeanObject,
    mut v_a_1247_: *mut crate::leanh::LeanObject,
    mut v_a_1248_: *mut crate::leanh::LeanObject,
    mut v_a_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_1245_, v_a_1247_);
    return v___x_1251_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubInt___boxed(
    mut v_e_1252_: *mut crate::leanh::LeanObject,
    mut v_a_1253_: *mut crate::leanh::LeanObject,
    mut v_a_1254_: *mut crate::leanh::LeanObject,
    mut v_a_1255_: *mut crate::leanh::LeanObject,
    mut v_a_1256_: *mut crate::leanh::LeanObject,
    mut v_a_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ =
        l_Lean_Meta_Structural_isInstSubInt(v_e_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
    crate::leanh::lean_dec(v_a_1256_);
    crate::leanh::lean_dec_ref(v_a_1255_);
    crate::leanh::lean_dec(v_a_1254_);
    crate::leanh::lean_dec_ref(v_a_1253_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulInt___redArg(
    mut v_e_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1278_: u8 = 0;
    let mut v_a_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1266_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1263_, v_a_1264_);
                if crate::leanh::lean_obj_tag(v___x_1266_) == 0 {
                    v_a_1267_ = crate::leanh::lean_ctor_get(v___x_1266_, 0);
                    v_isSharedCheck_1278_ = (!crate::leanh::lean_is_exclusive(v___x_1266_)) as u8;
                    if v_isSharedCheck_1278_ == 0 {
                        v___x_1269_ = v___x_1266_;
                        v_isShared_1270_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1267_);
                        crate::leanh::lean_dec(v___x_1266_);
                        v___x_1269_ = crate::leanh::lean_box(0);
                        v_isShared_1270_ = v_isSharedCheck_1278_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1279_ = crate::leanh::lean_ctor_get(v___x_1266_, 0);
                    v_isSharedCheck_1286_ = (!crate::leanh::lean_is_exclusive(v___x_1266_)) as u8;
                    if v_isSharedCheck_1286_ == 0 {
                        v___x_1281_ = v___x_1266_;
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1279_);
                        crate::leanh::lean_dec(v___x_1266_);
                        v___x_1281_ = crate::leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1286_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1271_ = l_Lean_Expr_cleanupAnnotations(v_a_1267_);
                v___x_1272_ = l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1;
                v___x_1273_ = l_Lean_Expr_isConstOf(v___x_1271_, v___x_1272_);
                crate::leanh::lean_dec_ref(v___x_1271_);
                v___x_1274_ = crate::leanh::lean_box((v___x_1273_) as usize);
                if v_isShared_1270_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1269_, 0, v___x_1274_);
                    v___x_1276_ = v___x_1269_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
                    v___x_1276_ = v_reuseFailAlloc_1277_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1276_;
            }
            3 => {
                if v_isShared_1282_ == 0 {
                    v___x_1284_ = v___x_1281_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1285_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulInt___redArg___boxed(
    mut v_e_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1290_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_1287_, v_a_1288_);
    crate::leanh::lean_dec(v_a_1288_);
    return v_res_1290_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulInt(
    mut v_e_1291_: *mut crate::leanh::LeanObject,
    mut v_a_1292_: *mut crate::leanh::LeanObject,
    mut v_a_1293_: *mut crate::leanh::LeanObject,
    mut v_a_1294_: *mut crate::leanh::LeanObject,
    mut v_a_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_1291_, v_a_1293_);
    return v___x_1297_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulInt___boxed(
    mut v_e_1298_: *mut crate::leanh::LeanObject,
    mut v_a_1299_: *mut crate::leanh::LeanObject,
    mut v_a_1300_: *mut crate::leanh::LeanObject,
    mut v_a_1301_: *mut crate::leanh::LeanObject,
    mut v_a_1302_: *mut crate::leanh::LeanObject,
    mut v_a_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1304_ =
        l_Lean_Meta_Structural_isInstMulInt(v_e_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
    crate::leanh::lean_dec(v_a_1302_);
    crate::leanh::lean_dec_ref(v_a_1301_);
    crate::leanh::lean_dec(v_a_1300_);
    crate::leanh::lean_dec_ref(v_a_1299_);
    return v_res_1304_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivInt___redArg(
    mut v_e_1309_: *mut crate::leanh::LeanObject,
    mut v_a_1310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1324_: u8 = 0;
    let mut v_a_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1328_: u8 = 0;
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1312_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1309_, v_a_1310_);
                if crate::leanh::lean_obj_tag(v___x_1312_) == 0 {
                    v_a_1313_ = crate::leanh::lean_ctor_get(v___x_1312_, 0);
                    v_isSharedCheck_1324_ = (!crate::leanh::lean_is_exclusive(v___x_1312_)) as u8;
                    if v_isSharedCheck_1324_ == 0 {
                        v___x_1315_ = v___x_1312_;
                        v_isShared_1316_ = v_isSharedCheck_1324_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1313_);
                        crate::leanh::lean_dec(v___x_1312_);
                        v___x_1315_ = crate::leanh::lean_box(0);
                        v_isShared_1316_ = v_isSharedCheck_1324_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1325_ = crate::leanh::lean_ctor_get(v___x_1312_, 0);
                    v_isSharedCheck_1332_ = (!crate::leanh::lean_is_exclusive(v___x_1312_)) as u8;
                    if v_isSharedCheck_1332_ == 0 {
                        v___x_1327_ = v___x_1312_;
                        v_isShared_1328_ = v_isSharedCheck_1332_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1325_);
                        crate::leanh::lean_dec(v___x_1312_);
                        v___x_1327_ = crate::leanh::lean_box(0);
                        v_isShared_1328_ = v_isSharedCheck_1332_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1317_ = l_Lean_Expr_cleanupAnnotations(v_a_1313_);
                v___x_1318_ = l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1;
                v___x_1319_ = l_Lean_Expr_isConstOf(v___x_1317_, v___x_1318_);
                crate::leanh::lean_dec_ref(v___x_1317_);
                v___x_1320_ = crate::leanh::lean_box((v___x_1319_) as usize);
                if v_isShared_1316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1315_, 0, v___x_1320_);
                    v___x_1322_ = v___x_1315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
                    v___x_1322_ = v_reuseFailAlloc_1323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1322_;
            }
            3 => {
                if v_isShared_1328_ == 0 {
                    v___x_1330_ = v___x_1327_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1331_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
                    v___x_1330_ = v_reuseFailAlloc_1331_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivInt___redArg___boxed(
    mut v_e_1333_: *mut crate::leanh::LeanObject,
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v_a_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_e_1333_, v_a_1334_);
    crate::leanh::lean_dec(v_a_1334_);
    return v_res_1336_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivInt(
    mut v_e_1337_: *mut crate::leanh::LeanObject,
    mut v_a_1338_: *mut crate::leanh::LeanObject,
    mut v_a_1339_: *mut crate::leanh::LeanObject,
    mut v_a_1340_: *mut crate::leanh::LeanObject,
    mut v_a_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1343_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_e_1337_, v_a_1339_);
    return v___x_1343_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivInt___boxed(
    mut v_e_1344_: *mut crate::leanh::LeanObject,
    mut v_a_1345_: *mut crate::leanh::LeanObject,
    mut v_a_1346_: *mut crate::leanh::LeanObject,
    mut v_a_1347_: *mut crate::leanh::LeanObject,
    mut v_a_1348_: *mut crate::leanh::LeanObject,
    mut v_a_1349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1350_ =
        l_Lean_Meta_Structural_isInstDivInt(v_e_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_);
    crate::leanh::lean_dec(v_a_1348_);
    crate::leanh::lean_dec_ref(v_a_1347_);
    crate::leanh::lean_dec(v_a_1346_);
    crate::leanh::lean_dec_ref(v_a_1345_);
    return v_res_1350_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstModInt___redArg(
    mut v_e_1355_: *mut crate::leanh::LeanObject,
    mut v_a_1356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut v_a_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1358_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1355_, v_a_1356_);
                if crate::leanh::lean_obj_tag(v___x_1358_) == 0 {
                    v_a_1359_ = crate::leanh::lean_ctor_get(v___x_1358_, 0);
                    v_isSharedCheck_1370_ = (!crate::leanh::lean_is_exclusive(v___x_1358_)) as u8;
                    if v_isSharedCheck_1370_ == 0 {
                        v___x_1361_ = v___x_1358_;
                        v_isShared_1362_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1359_);
                        crate::leanh::lean_dec(v___x_1358_);
                        v___x_1361_ = crate::leanh::lean_box(0);
                        v_isShared_1362_ = v_isSharedCheck_1370_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1371_ = crate::leanh::lean_ctor_get(v___x_1358_, 0);
                    v_isSharedCheck_1378_ = (!crate::leanh::lean_is_exclusive(v___x_1358_)) as u8;
                    if v_isSharedCheck_1378_ == 0 {
                        v___x_1373_ = v___x_1358_;
                        v_isShared_1374_ = v_isSharedCheck_1378_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1371_);
                        crate::leanh::lean_dec(v___x_1358_);
                        v___x_1373_ = crate::leanh::lean_box(0);
                        v_isShared_1374_ = v_isSharedCheck_1378_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1363_ = l_Lean_Expr_cleanupAnnotations(v_a_1359_);
                v___x_1364_ = l_Lean_Meta_Structural_isInstModInt___redArg___closed__1;
                v___x_1365_ = l_Lean_Expr_isConstOf(v___x_1363_, v___x_1364_);
                crate::leanh::lean_dec_ref(v___x_1363_);
                v___x_1366_ = crate::leanh::lean_box((v___x_1365_) as usize);
                if v_isShared_1362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1361_, 0, v___x_1366_);
                    v___x_1368_ = v___x_1361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
                    v___x_1368_ = v_reuseFailAlloc_1369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1368_;
            }
            3 => {
                if v_isShared_1374_ == 0 {
                    v___x_1376_ = v___x_1373_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1377_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstModInt___redArg___boxed(
    mut v_e_1379_: *mut crate::leanh::LeanObject,
    mut v_a_1380_: *mut crate::leanh::LeanObject,
    mut v_a_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_e_1379_, v_a_1380_);
    crate::leanh::lean_dec(v_a_1380_);
    return v_res_1382_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstModInt(
    mut v_e_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_e_1383_, v_a_1385_);
    return v___x_1389_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstModInt___boxed(
    mut v_e_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
    mut v_a_1394_: *mut crate::leanh::LeanObject,
    mut v_a_1395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ =
        l_Lean_Meta_Structural_isInstModInt(v_e_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
    crate::leanh::lean_dec(v_a_1394_);
    crate::leanh::lean_dec_ref(v_a_1393_);
    crate::leanh::lean_dec(v_a_1392_);
    crate::leanh::lean_dec_ref(v_a_1391_);
    return v_res_1396_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdInt___redArg(
    mut v_e_1401_: *mut crate::leanh::LeanObject,
    mut v_a_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1408_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut v_a_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1420_: u8 = 0;
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1424_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1404_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1401_, v_a_1402_);
                if crate::leanh::lean_obj_tag(v___x_1404_) == 0 {
                    v_a_1405_ = crate::leanh::lean_ctor_get(v___x_1404_, 0);
                    v_isSharedCheck_1416_ = (!crate::leanh::lean_is_exclusive(v___x_1404_)) as u8;
                    if v_isSharedCheck_1416_ == 0 {
                        v___x_1407_ = v___x_1404_;
                        v_isShared_1408_ = v_isSharedCheck_1416_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1405_);
                        crate::leanh::lean_dec(v___x_1404_);
                        v___x_1407_ = crate::leanh::lean_box(0);
                        v_isShared_1408_ = v_isSharedCheck_1416_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1417_ = crate::leanh::lean_ctor_get(v___x_1404_, 0);
                    v_isSharedCheck_1424_ = (!crate::leanh::lean_is_exclusive(v___x_1404_)) as u8;
                    if v_isSharedCheck_1424_ == 0 {
                        v___x_1419_ = v___x_1404_;
                        v_isShared_1420_ = v_isSharedCheck_1424_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1417_);
                        crate::leanh::lean_dec(v___x_1404_);
                        v___x_1419_ = crate::leanh::lean_box(0);
                        v_isShared_1420_ = v_isSharedCheck_1424_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1409_ = l_Lean_Expr_cleanupAnnotations(v_a_1405_);
                v___x_1410_ = l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1;
                v___x_1411_ = l_Lean_Expr_isConstOf(v___x_1409_, v___x_1410_);
                crate::leanh::lean_dec_ref(v___x_1409_);
                v___x_1412_ = crate::leanh::lean_box((v___x_1411_) as usize);
                if v_isShared_1408_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1407_, 0, v___x_1412_);
                    v___x_1414_ = v___x_1407_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
                    v___x_1414_ = v_reuseFailAlloc_1415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1414_;
            }
            3 => {
                if v_isShared_1420_ == 0 {
                    v___x_1422_ = v___x_1419_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1423_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
                    v___x_1422_ = v_reuseFailAlloc_1423_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdInt___redArg___boxed(
    mut v_e_1425_: *mut crate::leanh::LeanObject,
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1428_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_1425_, v_a_1426_);
    crate::leanh::lean_dec(v_a_1426_);
    return v_res_1428_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdInt(
    mut v_e_1429_: *mut crate::leanh::LeanObject,
    mut v_a_1430_: *mut crate::leanh::LeanObject,
    mut v_a_1431_: *mut crate::leanh::LeanObject,
    mut v_a_1432_: *mut crate::leanh::LeanObject,
    mut v_a_1433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1435_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_1429_, v_a_1431_);
    return v___x_1435_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdInt___boxed(
    mut v_e_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_a_1438_: *mut crate::leanh::LeanObject,
    mut v_a_1439_: *mut crate::leanh::LeanObject,
    mut v_a_1440_: *mut crate::leanh::LeanObject,
    mut v_a_1441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1442_ =
        l_Lean_Meta_Structural_isInstDvdInt(v_e_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
    crate::leanh::lean_dec(v_a_1440_);
    crate::leanh::lean_dec_ref(v_a_1439_);
    crate::leanh::lean_dec(v_a_1438_);
    crate::leanh::lean_dec_ref(v_a_1437_);
    return v_res_1442_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddInt___redArg(
    mut v_e_1446_: *mut crate::leanh::LeanObject,
    mut v_a_1447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u8 = 0;
    let mut v_arg_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut v_a_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1473_: u8 = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1449_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1446_, v_a_1447_);
                if crate::leanh::lean_obj_tag(v___x_1449_) == 0 {
                    v_a_1450_ = crate::leanh::lean_ctor_get(v___x_1449_, 0);
                    v_isSharedCheck_1469_ = (!crate::leanh::lean_is_exclusive(v___x_1449_)) as u8;
                    if v_isSharedCheck_1469_ == 0 {
                        v___x_1452_ = v___x_1449_;
                        v_isShared_1453_ = v_isSharedCheck_1469_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1450_);
                        crate::leanh::lean_dec(v___x_1449_);
                        v___x_1452_ = crate::leanh::lean_box(0);
                        v_isShared_1453_ = v_isSharedCheck_1469_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1470_ = crate::leanh::lean_ctor_get(v___x_1449_, 0);
                    v_isSharedCheck_1477_ = (!crate::leanh::lean_is_exclusive(v___x_1449_)) as u8;
                    if v_isSharedCheck_1477_ == 0 {
                        v___x_1472_ = v___x_1449_;
                        v_isShared_1473_ = v_isSharedCheck_1477_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1470_);
                        crate::leanh::lean_dec(v___x_1449_);
                        v___x_1472_ = crate::leanh::lean_box(0);
                        v_isShared_1473_ = v_isSharedCheck_1477_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1460_ = l_Lean_Expr_cleanupAnnotations(v_a_1450_);
                v___x_1461_ = l_Lean_Expr_isApp(v___x_1460_);
                if v___x_1461_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1460_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1462_ = crate::leanh::lean_ctor_get(v___x_1460_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1462_);
                    v___x_1463_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1460_);
                    v___x_1464_ = l_Lean_Expr_isApp(v___x_1463_);
                    if v___x_1464_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1463_);
                        crate::leanh::lean_dec_ref(v_arg_1462_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1465_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1463_);
                        v___x_1466_ = l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1;
                        v___x_1467_ = l_Lean_Expr_isConstOf(v___x_1465_, v___x_1466_);
                        crate::leanh::lean_dec_ref(v___x_1465_);
                        if v___x_1467_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1462_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1452_);
                            v___x_1468_ = l_Lean_Meta_Structural_isInstAddInt___redArg(
                                v_arg_1462_,
                                v_a_1447_,
                            );
                            return v___x_1468_;
                        }
                    }
                }
            }
            2 => {
                v___x_1455_ = 0;
                v___x_1456_ = crate::leanh::lean_box((v___x_1455_) as usize);
                if v_isShared_1453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1452_, 0, v___x_1456_);
                    v___x_1458_ = v___x_1452_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1459_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
                    v___x_1458_ = v_reuseFailAlloc_1459_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1458_;
            }
            4 => {
                if v_isShared_1473_ == 0 {
                    v___x_1475_ = v___x_1472_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
                    v___x_1475_ = v_reuseFailAlloc_1476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddInt___redArg___boxed(
    mut v_e_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1481_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_1478_, v_a_1479_);
    crate::leanh::lean_dec(v_a_1479_);
    return v_res_1481_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddInt(
    mut v_e_1482_: *mut crate::leanh::LeanObject,
    mut v_a_1483_: *mut crate::leanh::LeanObject,
    mut v_a_1484_: *mut crate::leanh::LeanObject,
    mut v_a_1485_: *mut crate::leanh::LeanObject,
    mut v_a_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1488_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_1482_, v_a_1484_);
    return v___x_1488_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddInt___boxed(
    mut v_e_1489_: *mut crate::leanh::LeanObject,
    mut v_a_1490_: *mut crate::leanh::LeanObject,
    mut v_a_1491_: *mut crate::leanh::LeanObject,
    mut v_a_1492_: *mut crate::leanh::LeanObject,
    mut v_a_1493_: *mut crate::leanh::LeanObject,
    mut v_a_1494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ =
        l_Lean_Meta_Structural_isInstHAddInt(v_e_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_);
    crate::leanh::lean_dec(v_a_1493_);
    crate::leanh::lean_dec_ref(v_a_1492_);
    crate::leanh::lean_dec(v_a_1491_);
    crate::leanh::lean_dec_ref(v_a_1490_);
    return v_res_1495_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubInt___redArg(
    mut v_e_1499_: *mut crate::leanh::LeanObject,
    mut v_a_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1506_: u8 = 0;
    let mut v___x_1508_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: u8 = 0;
    let mut v_arg_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1522_: u8 = 0;
    let mut v_a_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1526_: u8 = 0;
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1502_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1499_, v_a_1500_);
                if crate::leanh::lean_obj_tag(v___x_1502_) == 0 {
                    v_a_1503_ = crate::leanh::lean_ctor_get(v___x_1502_, 0);
                    v_isSharedCheck_1522_ = (!crate::leanh::lean_is_exclusive(v___x_1502_)) as u8;
                    if v_isSharedCheck_1522_ == 0 {
                        v___x_1505_ = v___x_1502_;
                        v_isShared_1506_ = v_isSharedCheck_1522_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1503_);
                        crate::leanh::lean_dec(v___x_1502_);
                        v___x_1505_ = crate::leanh::lean_box(0);
                        v_isShared_1506_ = v_isSharedCheck_1522_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1523_ = crate::leanh::lean_ctor_get(v___x_1502_, 0);
                    v_isSharedCheck_1530_ = (!crate::leanh::lean_is_exclusive(v___x_1502_)) as u8;
                    if v_isSharedCheck_1530_ == 0 {
                        v___x_1525_ = v___x_1502_;
                        v_isShared_1526_ = v_isSharedCheck_1530_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1523_);
                        crate::leanh::lean_dec(v___x_1502_);
                        v___x_1525_ = crate::leanh::lean_box(0);
                        v_isShared_1526_ = v_isSharedCheck_1530_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1513_ = l_Lean_Expr_cleanupAnnotations(v_a_1503_);
                v___x_1514_ = l_Lean_Expr_isApp(v___x_1513_);
                if v___x_1514_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1513_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1515_ = crate::leanh::lean_ctor_get(v___x_1513_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1515_);
                    v___x_1516_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1513_);
                    v___x_1517_ = l_Lean_Expr_isApp(v___x_1516_);
                    if v___x_1517_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1516_);
                        crate::leanh::lean_dec_ref(v_arg_1515_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1518_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1516_);
                        v___x_1519_ = l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1;
                        v___x_1520_ = l_Lean_Expr_isConstOf(v___x_1518_, v___x_1519_);
                        crate::leanh::lean_dec_ref(v___x_1518_);
                        if v___x_1520_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1515_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1505_);
                            v___x_1521_ = l_Lean_Meta_Structural_isInstSubInt___redArg(
                                v_arg_1515_,
                                v_a_1500_,
                            );
                            return v___x_1521_;
                        }
                    }
                }
            }
            2 => {
                v___x_1508_ = 0;
                v___x_1509_ = crate::leanh::lean_box((v___x_1508_) as usize);
                if v_isShared_1506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1509_);
                    v___x_1511_ = v___x_1505_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1509_);
                    v___x_1511_ = v_reuseFailAlloc_1512_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1511_;
            }
            4 => {
                if v_isShared_1526_ == 0 {
                    v___x_1528_ = v___x_1525_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
                    v___x_1528_ = v_reuseFailAlloc_1529_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubInt___redArg___boxed(
    mut v_e_1531_: *mut crate::leanh::LeanObject,
    mut v_a_1532_: *mut crate::leanh::LeanObject,
    mut v_a_1533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1534_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_1531_, v_a_1532_);
    crate::leanh::lean_dec(v_a_1532_);
    return v_res_1534_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubInt(
    mut v_e_1535_: *mut crate::leanh::LeanObject,
    mut v_a_1536_: *mut crate::leanh::LeanObject,
    mut v_a_1537_: *mut crate::leanh::LeanObject,
    mut v_a_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1541_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_1535_, v_a_1537_);
    return v___x_1541_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubInt___boxed(
    mut v_e_1542_: *mut crate::leanh::LeanObject,
    mut v_a_1543_: *mut crate::leanh::LeanObject,
    mut v_a_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1548_ =
        l_Lean_Meta_Structural_isInstHSubInt(v_e_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
    crate::leanh::lean_dec(v_a_1546_);
    crate::leanh::lean_dec_ref(v_a_1545_);
    crate::leanh::lean_dec(v_a_1544_);
    crate::leanh::lean_dec_ref(v_a_1543_);
    return v_res_1548_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulInt___redArg(
    mut v_e_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v_arg_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1575_: u8 = 0;
    let mut v_a_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1579_: u8 = 0;
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1583_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1555_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1552_, v_a_1553_);
                if crate::leanh::lean_obj_tag(v___x_1555_) == 0 {
                    v_a_1556_ = crate::leanh::lean_ctor_get(v___x_1555_, 0);
                    v_isSharedCheck_1575_ = (!crate::leanh::lean_is_exclusive(v___x_1555_)) as u8;
                    if v_isSharedCheck_1575_ == 0 {
                        v___x_1558_ = v___x_1555_;
                        v_isShared_1559_ = v_isSharedCheck_1575_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1556_);
                        crate::leanh::lean_dec(v___x_1555_);
                        v___x_1558_ = crate::leanh::lean_box(0);
                        v_isShared_1559_ = v_isSharedCheck_1575_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1576_ = crate::leanh::lean_ctor_get(v___x_1555_, 0);
                    v_isSharedCheck_1583_ = (!crate::leanh::lean_is_exclusive(v___x_1555_)) as u8;
                    if v_isSharedCheck_1583_ == 0 {
                        v___x_1578_ = v___x_1555_;
                        v_isShared_1579_ = v_isSharedCheck_1583_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1576_);
                        crate::leanh::lean_dec(v___x_1555_);
                        v___x_1578_ = crate::leanh::lean_box(0);
                        v_isShared_1579_ = v_isSharedCheck_1583_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1566_ = l_Lean_Expr_cleanupAnnotations(v_a_1556_);
                v___x_1567_ = l_Lean_Expr_isApp(v___x_1566_);
                if v___x_1567_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1566_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1568_ = crate::leanh::lean_ctor_get(v___x_1566_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1568_);
                    v___x_1569_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1566_);
                    v___x_1570_ = l_Lean_Expr_isApp(v___x_1569_);
                    if v___x_1570_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1569_);
                        crate::leanh::lean_dec_ref(v_arg_1568_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1571_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1569_);
                        v___x_1572_ = l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1;
                        v___x_1573_ = l_Lean_Expr_isConstOf(v___x_1571_, v___x_1572_);
                        crate::leanh::lean_dec_ref(v___x_1571_);
                        if v___x_1573_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1568_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1558_);
                            v___x_1574_ = l_Lean_Meta_Structural_isInstMulInt___redArg(
                                v_arg_1568_,
                                v_a_1553_,
                            );
                            return v___x_1574_;
                        }
                    }
                }
            }
            2 => {
                v___x_1561_ = 0;
                v___x_1562_ = crate::leanh::lean_box((v___x_1561_) as usize);
                if v_isShared_1559_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1558_, 0, v___x_1562_);
                    v___x_1564_ = v___x_1558_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
                    v___x_1564_ = v_reuseFailAlloc_1565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1564_;
            }
            4 => {
                if v_isShared_1579_ == 0 {
                    v___x_1581_ = v___x_1578_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
                    v___x_1581_ = v_reuseFailAlloc_1582_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulInt___redArg___boxed(
    mut v_e_1584_: *mut crate::leanh::LeanObject,
    mut v_a_1585_: *mut crate::leanh::LeanObject,
    mut v_a_1586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1587_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_1584_, v_a_1585_);
    crate::leanh::lean_dec(v_a_1585_);
    return v_res_1587_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulInt(
    mut v_e_1588_: *mut crate::leanh::LeanObject,
    mut v_a_1589_: *mut crate::leanh::LeanObject,
    mut v_a_1590_: *mut crate::leanh::LeanObject,
    mut v_a_1591_: *mut crate::leanh::LeanObject,
    mut v_a_1592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_1588_, v_a_1590_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulInt___boxed(
    mut v_e_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
    mut v_a_1597_: *mut crate::leanh::LeanObject,
    mut v_a_1598_: *mut crate::leanh::LeanObject,
    mut v_a_1599_: *mut crate::leanh::LeanObject,
    mut v_a_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ =
        l_Lean_Meta_Structural_isInstHMulInt(v_e_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
    crate::leanh::lean_dec(v_a_1599_);
    crate::leanh::lean_dec_ref(v_a_1598_);
    crate::leanh::lean_dec(v_a_1597_);
    crate::leanh::lean_dec_ref(v_a_1596_);
    return v_res_1601_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivInt___redArg(
    mut v_e_1605_: *mut crate::leanh::LeanObject,
    mut v_a_1606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: u8 = 0;
    let mut v_arg_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1628_: u8 = 0;
    let mut v_a_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1632_: u8 = 0;
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1608_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1605_, v_a_1606_);
                if crate::leanh::lean_obj_tag(v___x_1608_) == 0 {
                    v_a_1609_ = crate::leanh::lean_ctor_get(v___x_1608_, 0);
                    v_isSharedCheck_1628_ = (!crate::leanh::lean_is_exclusive(v___x_1608_)) as u8;
                    if v_isSharedCheck_1628_ == 0 {
                        v___x_1611_ = v___x_1608_;
                        v_isShared_1612_ = v_isSharedCheck_1628_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1609_);
                        crate::leanh::lean_dec(v___x_1608_);
                        v___x_1611_ = crate::leanh::lean_box(0);
                        v_isShared_1612_ = v_isSharedCheck_1628_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1629_ = crate::leanh::lean_ctor_get(v___x_1608_, 0);
                    v_isSharedCheck_1636_ = (!crate::leanh::lean_is_exclusive(v___x_1608_)) as u8;
                    if v_isSharedCheck_1636_ == 0 {
                        v___x_1631_ = v___x_1608_;
                        v_isShared_1632_ = v_isSharedCheck_1636_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1629_);
                        crate::leanh::lean_dec(v___x_1608_);
                        v___x_1631_ = crate::leanh::lean_box(0);
                        v_isShared_1632_ = v_isSharedCheck_1636_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1619_ = l_Lean_Expr_cleanupAnnotations(v_a_1609_);
                v___x_1620_ = l_Lean_Expr_isApp(v___x_1619_);
                if v___x_1620_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1619_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1621_ = crate::leanh::lean_ctor_get(v___x_1619_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1621_);
                    v___x_1622_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1619_);
                    v___x_1623_ = l_Lean_Expr_isApp(v___x_1622_);
                    if v___x_1623_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1622_);
                        crate::leanh::lean_dec_ref(v_arg_1621_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1624_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1622_);
                        v___x_1625_ = l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1;
                        v___x_1626_ = l_Lean_Expr_isConstOf(v___x_1624_, v___x_1625_);
                        crate::leanh::lean_dec_ref(v___x_1624_);
                        if v___x_1626_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1621_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1611_);
                            v___x_1627_ = l_Lean_Meta_Structural_isInstDivInt___redArg(
                                v_arg_1621_,
                                v_a_1606_,
                            );
                            return v___x_1627_;
                        }
                    }
                }
            }
            2 => {
                v___x_1614_ = 0;
                v___x_1615_ = crate::leanh::lean_box((v___x_1614_) as usize);
                if v_isShared_1612_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1611_, 0, v___x_1615_);
                    v___x_1617_ = v___x_1611_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
                    v___x_1617_ = v_reuseFailAlloc_1618_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1617_;
            }
            4 => {
                if v_isShared_1632_ == 0 {
                    v___x_1634_ = v___x_1631_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
                    v___x_1634_ = v_reuseFailAlloc_1635_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivInt___redArg___boxed(
    mut v_e_1637_: *mut crate::leanh::LeanObject,
    mut v_a_1638_: *mut crate::leanh::LeanObject,
    mut v_a_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1640_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_e_1637_, v_a_1638_);
    crate::leanh::lean_dec(v_a_1638_);
    return v_res_1640_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivInt(
    mut v_e_1641_: *mut crate::leanh::LeanObject,
    mut v_a_1642_: *mut crate::leanh::LeanObject,
    mut v_a_1643_: *mut crate::leanh::LeanObject,
    mut v_a_1644_: *mut crate::leanh::LeanObject,
    mut v_a_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_e_1641_, v_a_1643_);
    return v___x_1647_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivInt___boxed(
    mut v_e_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
    mut v_a_1652_: *mut crate::leanh::LeanObject,
    mut v_a_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1654_ =
        l_Lean_Meta_Structural_isInstHDivInt(v_e_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
    crate::leanh::lean_dec(v_a_1652_);
    crate::leanh::lean_dec_ref(v_a_1651_);
    crate::leanh::lean_dec(v_a_1650_);
    crate::leanh::lean_dec_ref(v_a_1649_);
    return v_res_1654_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModInt___redArg(
    mut v_e_1658_: *mut crate::leanh::LeanObject,
    mut v_a_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1665_: u8 = 0;
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v_arg_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1681_: u8 = 0;
    let mut v_a_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1685_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1658_, v_a_1659_);
                if crate::leanh::lean_obj_tag(v___x_1661_) == 0 {
                    v_a_1662_ = crate::leanh::lean_ctor_get(v___x_1661_, 0);
                    v_isSharedCheck_1681_ = (!crate::leanh::lean_is_exclusive(v___x_1661_)) as u8;
                    if v_isSharedCheck_1681_ == 0 {
                        v___x_1664_ = v___x_1661_;
                        v_isShared_1665_ = v_isSharedCheck_1681_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1662_);
                        crate::leanh::lean_dec(v___x_1661_);
                        v___x_1664_ = crate::leanh::lean_box(0);
                        v_isShared_1665_ = v_isSharedCheck_1681_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1682_ = crate::leanh::lean_ctor_get(v___x_1661_, 0);
                    v_isSharedCheck_1689_ = (!crate::leanh::lean_is_exclusive(v___x_1661_)) as u8;
                    if v_isSharedCheck_1689_ == 0 {
                        v___x_1684_ = v___x_1661_;
                        v_isShared_1685_ = v_isSharedCheck_1689_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1682_);
                        crate::leanh::lean_dec(v___x_1661_);
                        v___x_1684_ = crate::leanh::lean_box(0);
                        v_isShared_1685_ = v_isSharedCheck_1689_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1672_ = l_Lean_Expr_cleanupAnnotations(v_a_1662_);
                v___x_1673_ = l_Lean_Expr_isApp(v___x_1672_);
                if v___x_1673_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1672_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1674_ = crate::leanh::lean_ctor_get(v___x_1672_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1674_);
                    v___x_1675_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1672_);
                    v___x_1676_ = l_Lean_Expr_isApp(v___x_1675_);
                    if v___x_1676_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1675_);
                        crate::leanh::lean_dec_ref(v_arg_1674_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1677_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1675_);
                        v___x_1678_ = l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1;
                        v___x_1679_ = l_Lean_Expr_isConstOf(v___x_1677_, v___x_1678_);
                        crate::leanh::lean_dec_ref(v___x_1677_);
                        if v___x_1679_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1674_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1664_);
                            v___x_1680_ = l_Lean_Meta_Structural_isInstModInt___redArg(
                                v_arg_1674_,
                                v_a_1659_,
                            );
                            return v___x_1680_;
                        }
                    }
                }
            }
            2 => {
                v___x_1667_ = 0;
                v___x_1668_ = crate::leanh::lean_box((v___x_1667_) as usize);
                if v_isShared_1665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1664_, 0, v___x_1668_);
                    v___x_1670_ = v___x_1664_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
                    v___x_1670_ = v_reuseFailAlloc_1671_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1670_;
            }
            4 => {
                if v_isShared_1685_ == 0 {
                    v___x_1687_ = v___x_1684_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
                    v___x_1687_ = v_reuseFailAlloc_1688_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModInt___redArg___boxed(
    mut v_e_1690_: *mut crate::leanh::LeanObject,
    mut v_a_1691_: *mut crate::leanh::LeanObject,
    mut v_a_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_e_1690_, v_a_1691_);
    crate::leanh::lean_dec(v_a_1691_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModInt(
    mut v_e_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
    mut v_a_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
    mut v_a_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_e_1694_, v_a_1696_);
    return v___x_1700_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModInt___boxed(
    mut v_e_1701_: *mut crate::leanh::LeanObject,
    mut v_a_1702_: *mut crate::leanh::LeanObject,
    mut v_a_1703_: *mut crate::leanh::LeanObject,
    mut v_a_1704_: *mut crate::leanh::LeanObject,
    mut v_a_1705_: *mut crate::leanh::LeanObject,
    mut v_a_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ =
        l_Lean_Meta_Structural_isInstHModInt(v_e_1701_, v_a_1702_, v_a_1703_, v_a_1704_, v_a_1705_);
    crate::leanh::lean_dec(v_a_1705_);
    crate::leanh::lean_dec_ref(v_a_1704_);
    crate::leanh::lean_dec(v_a_1703_);
    crate::leanh::lean_dec_ref(v_a_1702_);
    return v_res_1707_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTInt___redArg(
    mut v_e_1712_: *mut crate::leanh::LeanObject,
    mut v_a_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_a_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1715_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1712_, v_a_1713_);
                if crate::leanh::lean_obj_tag(v___x_1715_) == 0 {
                    v_a_1716_ = crate::leanh::lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1727_ = (!crate::leanh::lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1727_ == 0 {
                        v___x_1718_ = v___x_1715_;
                        v_isShared_1719_ = v_isSharedCheck_1727_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1716_);
                        crate::leanh::lean_dec(v___x_1715_);
                        v___x_1718_ = crate::leanh::lean_box(0);
                        v_isShared_1719_ = v_isSharedCheck_1727_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1728_ = crate::leanh::lean_ctor_get(v___x_1715_, 0);
                    v_isSharedCheck_1735_ = (!crate::leanh::lean_is_exclusive(v___x_1715_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1730_ = v___x_1715_;
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1728_);
                        crate::leanh::lean_dec(v___x_1715_);
                        v___x_1730_ = crate::leanh::lean_box(0);
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1720_ = l_Lean_Expr_cleanupAnnotations(v_a_1716_);
                v___x_1721_ = l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1;
                v___x_1722_ = l_Lean_Expr_isConstOf(v___x_1720_, v___x_1721_);
                crate::leanh::lean_dec_ref(v___x_1720_);
                v___x_1723_ = crate::leanh::lean_box((v___x_1722_) as usize);
                if v_isShared_1719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1723_);
                    v___x_1725_ = v___x_1718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
                    v___x_1725_ = v_reuseFailAlloc_1726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1725_;
            }
            3 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTInt___redArg___boxed(
    mut v_e_1736_: *mut crate::leanh::LeanObject,
    mut v_a_1737_: *mut crate::leanh::LeanObject,
    mut v_a_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_1736_, v_a_1737_);
    crate::leanh::lean_dec(v_a_1737_);
    return v_res_1739_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTInt(
    mut v_e_1740_: *mut crate::leanh::LeanObject,
    mut v_a_1741_: *mut crate::leanh::LeanObject,
    mut v_a_1742_: *mut crate::leanh::LeanObject,
    mut v_a_1743_: *mut crate::leanh::LeanObject,
    mut v_a_1744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1746_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_1740_, v_a_1742_);
    return v___x_1746_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTInt___boxed(
    mut v_e_1747_: *mut crate::leanh::LeanObject,
    mut v_a_1748_: *mut crate::leanh::LeanObject,
    mut v_a_1749_: *mut crate::leanh::LeanObject,
    mut v_a_1750_: *mut crate::leanh::LeanObject,
    mut v_a_1751_: *mut crate::leanh::LeanObject,
    mut v_a_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1753_ =
        l_Lean_Meta_Structural_isInstLTInt(v_e_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
    crate::leanh::lean_dec(v_a_1751_);
    crate::leanh::lean_dec_ref(v_a_1750_);
    crate::leanh::lean_dec(v_a_1749_);
    crate::leanh::lean_dec_ref(v_a_1748_);
    return v_res_1753_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLEInt___redArg(
    mut v_e_1758_: *mut crate::leanh::LeanObject,
    mut v_a_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_a_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1777_: u8 = 0;
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1761_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1758_, v_a_1759_);
                if crate::leanh::lean_obj_tag(v___x_1761_) == 0 {
                    v_a_1762_ = crate::leanh::lean_ctor_get(v___x_1761_, 0);
                    v_isSharedCheck_1773_ = (!crate::leanh::lean_is_exclusive(v___x_1761_)) as u8;
                    if v_isSharedCheck_1773_ == 0 {
                        v___x_1764_ = v___x_1761_;
                        v_isShared_1765_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1762_);
                        crate::leanh::lean_dec(v___x_1761_);
                        v___x_1764_ = crate::leanh::lean_box(0);
                        v_isShared_1765_ = v_isSharedCheck_1773_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1774_ = crate::leanh::lean_ctor_get(v___x_1761_, 0);
                    v_isSharedCheck_1781_ = (!crate::leanh::lean_is_exclusive(v___x_1761_)) as u8;
                    if v_isSharedCheck_1781_ == 0 {
                        v___x_1776_ = v___x_1761_;
                        v_isShared_1777_ = v_isSharedCheck_1781_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1774_);
                        crate::leanh::lean_dec(v___x_1761_);
                        v___x_1776_ = crate::leanh::lean_box(0);
                        v_isShared_1777_ = v_isSharedCheck_1781_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1766_ = l_Lean_Expr_cleanupAnnotations(v_a_1762_);
                v___x_1767_ = l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1;
                v___x_1768_ = l_Lean_Expr_isConstOf(v___x_1766_, v___x_1767_);
                crate::leanh::lean_dec_ref(v___x_1766_);
                v___x_1769_ = crate::leanh::lean_box((v___x_1768_) as usize);
                if v_isShared_1765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1764_, 0, v___x_1769_);
                    v___x_1771_ = v___x_1764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
                    v___x_1771_ = v_reuseFailAlloc_1772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1771_;
            }
            3 => {
                if v_isShared_1777_ == 0 {
                    v___x_1779_ = v___x_1776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
                    v___x_1779_ = v_reuseFailAlloc_1780_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstLEInt___redArg___boxed(
    mut v_e_1782_: *mut crate::leanh::LeanObject,
    mut v_a_1783_: *mut crate::leanh::LeanObject,
    mut v_a_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_1782_, v_a_1783_);
    crate::leanh::lean_dec(v_a_1783_);
    return v_res_1785_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLEInt(
    mut v_e_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
    mut v_a_1789_: *mut crate::leanh::LeanObject,
    mut v_a_1790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_1786_, v_a_1788_);
    return v___x_1792_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLEInt___boxed(
    mut v_e_1793_: *mut crate::leanh::LeanObject,
    mut v_a_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1799_ =
        l_Lean_Meta_Structural_isInstLEInt(v_e_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_);
    crate::leanh::lean_dec(v_a_1797_);
    crate::leanh::lean_dec_ref(v_a_1796_);
    crate::leanh::lean_dec(v_a_1795_);
    crate::leanh::lean_dec_ref(v_a_1794_);
    return v_res_1799_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowInt___redArg(
    mut v_e_1804_: *mut crate::leanh::LeanObject,
    mut v_a_1805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1811_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: u8 = 0;
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut v_a_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1807_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1804_, v_a_1805_);
                if crate::leanh::lean_obj_tag(v___x_1807_) == 0 {
                    v_a_1808_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                    v_isSharedCheck_1819_ = (!crate::leanh::lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1810_ = v___x_1807_;
                        v_isShared_1811_ = v_isSharedCheck_1819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1808_);
                        crate::leanh::lean_dec(v___x_1807_);
                        v___x_1810_ = crate::leanh::lean_box(0);
                        v_isShared_1811_ = v_isSharedCheck_1819_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1820_ = crate::leanh::lean_ctor_get(v___x_1807_, 0);
                    v_isSharedCheck_1827_ = (!crate::leanh::lean_is_exclusive(v___x_1807_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1822_ = v___x_1807_;
                        v_isShared_1823_ = v_isSharedCheck_1827_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1820_);
                        crate::leanh::lean_dec(v___x_1807_);
                        v___x_1822_ = crate::leanh::lean_box(0);
                        v_isShared_1823_ = v_isSharedCheck_1827_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1812_ = l_Lean_Expr_cleanupAnnotations(v_a_1808_);
                v___x_1813_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1;
                v___x_1814_ = l_Lean_Expr_isConstOf(v___x_1812_, v___x_1813_);
                crate::leanh::lean_dec_ref(v___x_1812_);
                v___x_1815_ = crate::leanh::lean_box((v___x_1814_) as usize);
                if v_isShared_1811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1810_, 0, v___x_1815_);
                    v___x_1817_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1818_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
                    v___x_1817_ = v_reuseFailAlloc_1818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1817_;
            }
            3 => {
                if v_isShared_1823_ == 0 {
                    v___x_1825_ = v___x_1822_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1825_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowInt___redArg___boxed(
    mut v_e_1828_: *mut crate::leanh::LeanObject,
    mut v_a_1829_: *mut crate::leanh::LeanObject,
    mut v_a_1830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1831_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_e_1828_, v_a_1829_);
    crate::leanh::lean_dec(v_a_1829_);
    return v_res_1831_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowInt(
    mut v_e_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_e_1832_, v_a_1834_);
    return v___x_1838_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowInt___boxed(
    mut v_e_1839_: *mut crate::leanh::LeanObject,
    mut v_a_1840_: *mut crate::leanh::LeanObject,
    mut v_a_1841_: *mut crate::leanh::LeanObject,
    mut v_a_1842_: *mut crate::leanh::LeanObject,
    mut v_a_1843_: *mut crate::leanh::LeanObject,
    mut v_a_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l_Lean_Meta_Structural_isInstNatPowInt(
        v_e_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_,
    );
    crate::leanh::lean_dec(v_a_1843_);
    crate::leanh::lean_dec_ref(v_a_1842_);
    crate::leanh::lean_dec(v_a_1841_);
    crate::leanh::lean_dec_ref(v_a_1840_);
    return v_res_1845_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowInt___redArg(
    mut v_e_1849_: *mut crate::leanh::LeanObject,
    mut v_a_1850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1856_: u8 = 0;
    let mut v___x_1858_: u8 = 0;
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v_arg_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: u8 = 0;
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_a_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1876_: u8 = 0;
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1852_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1849_, v_a_1850_);
                if crate::leanh::lean_obj_tag(v___x_1852_) == 0 {
                    v_a_1853_ = crate::leanh::lean_ctor_get(v___x_1852_, 0);
                    v_isSharedCheck_1872_ = (!crate::leanh::lean_is_exclusive(v___x_1852_)) as u8;
                    if v_isSharedCheck_1872_ == 0 {
                        v___x_1855_ = v___x_1852_;
                        v_isShared_1856_ = v_isSharedCheck_1872_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1853_);
                        crate::leanh::lean_dec(v___x_1852_);
                        v___x_1855_ = crate::leanh::lean_box(0);
                        v_isShared_1856_ = v_isSharedCheck_1872_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1873_ = crate::leanh::lean_ctor_get(v___x_1852_, 0);
                    v_isSharedCheck_1880_ = (!crate::leanh::lean_is_exclusive(v___x_1852_)) as u8;
                    if v_isSharedCheck_1880_ == 0 {
                        v___x_1875_ = v___x_1852_;
                        v_isShared_1876_ = v_isSharedCheck_1880_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1873_);
                        crate::leanh::lean_dec(v___x_1852_);
                        v___x_1875_ = crate::leanh::lean_box(0);
                        v_isShared_1876_ = v_isSharedCheck_1880_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1863_ = l_Lean_Expr_cleanupAnnotations(v_a_1853_);
                v___x_1864_ = l_Lean_Expr_isApp(v___x_1863_);
                if v___x_1864_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1863_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1865_ = crate::leanh::lean_ctor_get(v___x_1863_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1865_);
                    v___x_1866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1863_);
                    v___x_1867_ = l_Lean_Expr_isApp(v___x_1866_);
                    if v___x_1867_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1866_);
                        crate::leanh::lean_dec_ref(v_arg_1865_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1868_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1866_);
                        v___x_1869_ = l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1;
                        v___x_1870_ = l_Lean_Expr_isConstOf(v___x_1868_, v___x_1869_);
                        crate::leanh::lean_dec_ref(v___x_1868_);
                        if v___x_1870_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_1865_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_1855_);
                            v___x_1871_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(
                                v_arg_1865_,
                                v_a_1850_,
                            );
                            return v___x_1871_;
                        }
                    }
                }
            }
            2 => {
                v___x_1858_ = 0;
                v___x_1859_ = crate::leanh::lean_box((v___x_1858_) as usize);
                if v_isShared_1856_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1855_, 0, v___x_1859_);
                    v___x_1861_ = v___x_1855_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1862_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
                    v___x_1861_ = v_reuseFailAlloc_1862_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1861_;
            }
            4 => {
                if v_isShared_1876_ == 0 {
                    v___x_1878_ = v___x_1875_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
                    v___x_1878_ = v_reuseFailAlloc_1879_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowInt___redArg___boxed(
    mut v_e_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_e_1881_, v_a_1882_);
    crate::leanh::lean_dec(v_a_1882_);
    return v_res_1884_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowInt(
    mut v_e_1885_: *mut crate::leanh::LeanObject,
    mut v_a_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_e_1885_, v_a_1887_);
    return v___x_1891_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowInt___boxed(
    mut v_e_1892_: *mut crate::leanh::LeanObject,
    mut v_a_1893_: *mut crate::leanh::LeanObject,
    mut v_a_1894_: *mut crate::leanh::LeanObject,
    mut v_a_1895_: *mut crate::leanh::LeanObject,
    mut v_a_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1898_ =
        l_Lean_Meta_Structural_isInstPowInt(v_e_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_);
    crate::leanh::lean_dec(v_a_1896_);
    crate::leanh::lean_dec_ref(v_a_1895_);
    crate::leanh::lean_dec(v_a_1894_);
    crate::leanh::lean_dec_ref(v_a_1893_);
    return v_res_1898_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowInt___redArg(
    mut v_e_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1909_: u8 = 0;
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    let mut v_arg_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: u8 = 0;
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut v_a_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1905_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1902_, v_a_1903_);
                if crate::leanh::lean_obj_tag(v___x_1905_) == 0 {
                    v_a_1906_ = crate::leanh::lean_ctor_get(v___x_1905_, 0);
                    v_isSharedCheck_1927_ = (!crate::leanh::lean_is_exclusive(v___x_1905_)) as u8;
                    if v_isSharedCheck_1927_ == 0 {
                        v___x_1908_ = v___x_1905_;
                        v_isShared_1909_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1906_);
                        crate::leanh::lean_dec(v___x_1905_);
                        v___x_1908_ = crate::leanh::lean_box(0);
                        v_isShared_1909_ = v_isSharedCheck_1927_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1928_ = crate::leanh::lean_ctor_get(v___x_1905_, 0);
                    v_isSharedCheck_1935_ = (!crate::leanh::lean_is_exclusive(v___x_1905_)) as u8;
                    if v_isSharedCheck_1935_ == 0 {
                        v___x_1930_ = v___x_1905_;
                        v_isShared_1931_ = v_isSharedCheck_1935_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1928_);
                        crate::leanh::lean_dec(v___x_1905_);
                        v___x_1930_ = crate::leanh::lean_box(0);
                        v_isShared_1931_ = v_isSharedCheck_1935_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1916_ = l_Lean_Expr_cleanupAnnotations(v_a_1906_);
                v___x_1917_ = l_Lean_Expr_isApp(v___x_1916_);
                if v___x_1917_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_1916_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1918_ = crate::leanh::lean_ctor_get(v___x_1916_, 1);
                    crate::leanh::lean_inc_ref(v_arg_1918_);
                    v___x_1919_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1916_);
                    v___x_1920_ = l_Lean_Expr_isApp(v___x_1919_);
                    if v___x_1920_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1919_);
                        crate::leanh::lean_dec_ref(v_arg_1918_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1921_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1919_);
                        v___x_1922_ = l_Lean_Expr_isApp(v___x_1921_);
                        if v___x_1922_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1921_);
                            crate::leanh::lean_dec_ref(v_arg_1918_);
                            state = 2;
                            continue;
                        } else {
                            v___x_1923_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1921_);
                            v___x_1924_ = l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1;
                            v___x_1925_ = l_Lean_Expr_isConstOf(v___x_1923_, v___x_1924_);
                            crate::leanh::lean_dec_ref(v___x_1923_);
                            if v___x_1925_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_1918_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_1908_);
                                v___x_1926_ = l_Lean_Meta_Structural_isInstPowInt___redArg(
                                    v_arg_1918_,
                                    v_a_1903_,
                                );
                                return v___x_1926_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1911_ = 0;
                v___x_1912_ = crate::leanh::lean_box((v___x_1911_) as usize);
                if v_isShared_1909_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1908_, 0, v___x_1912_);
                    v___x_1914_ = v___x_1908_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
                    v___x_1914_ = v_reuseFailAlloc_1915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1914_;
            }
            4 => {
                if v_isShared_1931_ == 0 {
                    v___x_1933_ = v___x_1930_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
                    v___x_1933_ = v_reuseFailAlloc_1934_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowInt___redArg___boxed(
    mut v_e_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
    mut v_a_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1939_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_e_1936_, v_a_1937_);
    crate::leanh::lean_dec(v_a_1937_);
    return v_res_1939_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowInt(
    mut v_e_1940_: *mut crate::leanh::LeanObject,
    mut v_a_1941_: *mut crate::leanh::LeanObject,
    mut v_a_1942_: *mut crate::leanh::LeanObject,
    mut v_a_1943_: *mut crate::leanh::LeanObject,
    mut v_a_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_e_1940_, v_a_1942_);
    return v___x_1946_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowInt___boxed(
    mut v_e_1947_: *mut crate::leanh::LeanObject,
    mut v_a_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1953_ =
        l_Lean_Meta_Structural_isInstHPowInt(v_e_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
    crate::leanh::lean_dec(v_a_1951_);
    crate::leanh::lean_dec_ref(v_a_1950_);
    crate::leanh::lean_dec(v_a_1949_);
    crate::leanh::lean_dec_ref(v_a_1948_);
    return v_res_1953_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstNegInt(
    mut v_e_1954_: *mut crate::leanh::LeanObject,
    mut v_a_1955_: *mut crate::leanh::LeanObject,
    mut v_a_1956_: *mut crate::leanh::LeanObject,
    mut v_a_1957_: *mut crate::leanh::LeanObject,
    mut v_a_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_1954_);
    v___x_1960_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_1954_, v_a_1956_);
    if crate::leanh::lean_obj_tag(v___x_1960_) == 0 {
        let mut v_a_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1962_: u8 = 0;
        v_a_1961_ = crate::leanh::lean_ctor_get(v___x_1960_, 0);
        crate::leanh::lean_inc(v_a_1961_);
        v___x_1962_ = (crate::leanh::lean_unbox(v_a_1961_) as u8);
        crate::leanh::lean_dec(v_a_1961_);
        if v___x_1962_ == 0 {
            let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1960_, 1);
            v___x_1963_ = l_Lean_Int_mkInstNeg;
            v___x_1964_ = l_Lean_Meta_isDefEqI(
                v_e_1954_,
                v___x_1963_,
                v_a_1955_,
                v_a_1956_,
                v_a_1957_,
                v_a_1958_,
            );
            return v___x_1964_;
        } else {
            crate::leanh::lean_dec_ref(v_e_1954_);
            return v___x_1960_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_1954_);
        return v___x_1960_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstNegInt___boxed(
    mut v_e_1965_: *mut crate::leanh::LeanObject,
    mut v_a_1966_: *mut crate::leanh::LeanObject,
    mut v_a_1967_: *mut crate::leanh::LeanObject,
    mut v_a_1968_: *mut crate::leanh::LeanObject,
    mut v_a_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1971_ =
        l_Lean_Meta_DefEq_isInstNegInt(v_e_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_);
    crate::leanh::lean_dec(v_a_1969_);
    crate::leanh::lean_dec_ref(v_a_1968_);
    crate::leanh::lean_dec(v_a_1967_);
    crate::leanh::lean_dec_ref(v_a_1966_);
    return v_res_1971_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstAddInt(
    mut v_e_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
    mut v_a_1975_: *mut crate::leanh::LeanObject,
    mut v_a_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_1972_);
    v___x_1978_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_1972_, v_a_1974_);
    if crate::leanh::lean_obj_tag(v___x_1978_) == 0 {
        let mut v_a_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1980_: u8 = 0;
        v_a_1979_ = crate::leanh::lean_ctor_get(v___x_1978_, 0);
        crate::leanh::lean_inc(v_a_1979_);
        v___x_1980_ = (crate::leanh::lean_unbox(v_a_1979_) as u8);
        crate::leanh::lean_dec(v_a_1979_);
        if v___x_1980_ == 0 {
            let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1978_, 1);
            v___x_1981_ = l_Lean_Int_mkInstAdd;
            v___x_1982_ = l_Lean_Meta_isDefEqI(
                v_e_1972_,
                v___x_1981_,
                v_a_1973_,
                v_a_1974_,
                v_a_1975_,
                v_a_1976_,
            );
            return v___x_1982_;
        } else {
            crate::leanh::lean_dec_ref(v_e_1972_);
            return v___x_1978_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_1972_);
        return v___x_1978_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstAddInt___boxed(
    mut v_e_1983_: *mut crate::leanh::LeanObject,
    mut v_a_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
    mut v_a_1987_: *mut crate::leanh::LeanObject,
    mut v_a_1988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1989_ =
        l_Lean_Meta_DefEq_isInstAddInt(v_e_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_);
    crate::leanh::lean_dec(v_a_1987_);
    crate::leanh::lean_dec_ref(v_a_1986_);
    crate::leanh::lean_dec(v_a_1985_);
    crate::leanh::lean_dec_ref(v_a_1984_);
    return v_res_1989_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHAddInt(
    mut v_e_1990_: *mut crate::leanh::LeanObject,
    mut v_a_1991_: *mut crate::leanh::LeanObject,
    mut v_a_1992_: *mut crate::leanh::LeanObject,
    mut v_a_1993_: *mut crate::leanh::LeanObject,
    mut v_a_1994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_1990_);
    v___x_1996_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_1990_, v_a_1992_);
    if crate::leanh::lean_obj_tag(v___x_1996_) == 0 {
        let mut v_a_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1998_: u8 = 0;
        v_a_1997_ = crate::leanh::lean_ctor_get(v___x_1996_, 0);
        crate::leanh::lean_inc(v_a_1997_);
        v___x_1998_ = (crate::leanh::lean_unbox(v_a_1997_) as u8);
        crate::leanh::lean_dec(v_a_1997_);
        if v___x_1998_ == 0 {
            let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1996_, 1);
            v___x_1999_ = l_Lean_Int_mkInstHAdd;
            v___x_2000_ = l_Lean_Meta_isDefEqI(
                v_e_1990_,
                v___x_1999_,
                v_a_1991_,
                v_a_1992_,
                v_a_1993_,
                v_a_1994_,
            );
            return v___x_2000_;
        } else {
            crate::leanh::lean_dec_ref(v_e_1990_);
            return v___x_1996_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_1990_);
        return v___x_1996_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHAddInt___boxed(
    mut v_e_2001_: *mut crate::leanh::LeanObject,
    mut v_a_2002_: *mut crate::leanh::LeanObject,
    mut v_a_2003_: *mut crate::leanh::LeanObject,
    mut v_a_2004_: *mut crate::leanh::LeanObject,
    mut v_a_2005_: *mut crate::leanh::LeanObject,
    mut v_a_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2007_ =
        l_Lean_Meta_DefEq_isInstHAddInt(v_e_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
    crate::leanh::lean_dec(v_a_2005_);
    crate::leanh::lean_dec_ref(v_a_2004_);
    crate::leanh::lean_dec(v_a_2003_);
    crate::leanh::lean_dec_ref(v_a_2002_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstSubInt(
    mut v_e_2008_: *mut crate::leanh::LeanObject,
    mut v_a_2009_: *mut crate::leanh::LeanObject,
    mut v_a_2010_: *mut crate::leanh::LeanObject,
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_a_2012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2008_);
    v___x_2014_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_2008_, v_a_2010_);
    if crate::leanh::lean_obj_tag(v___x_2014_) == 0 {
        let mut v_a_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2016_: u8 = 0;
        v_a_2015_ = crate::leanh::lean_ctor_get(v___x_2014_, 0);
        crate::leanh::lean_inc(v_a_2015_);
        v___x_2016_ = (crate::leanh::lean_unbox(v_a_2015_) as u8);
        crate::leanh::lean_dec(v_a_2015_);
        if v___x_2016_ == 0 {
            let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2014_, 1);
            v___x_2017_ = l_Lean_Int_mkInstSub;
            v___x_2018_ = l_Lean_Meta_isDefEqI(
                v_e_2008_,
                v___x_2017_,
                v_a_2009_,
                v_a_2010_,
                v_a_2011_,
                v_a_2012_,
            );
            return v___x_2018_;
        } else {
            crate::leanh::lean_dec_ref(v_e_2008_);
            return v___x_2014_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_2008_);
        return v___x_2014_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstSubInt___boxed(
    mut v_e_2019_: *mut crate::leanh::LeanObject,
    mut v_a_2020_: *mut crate::leanh::LeanObject,
    mut v_a_2021_: *mut crate::leanh::LeanObject,
    mut v_a_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ =
        l_Lean_Meta_DefEq_isInstSubInt(v_e_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
    crate::leanh::lean_dec(v_a_2023_);
    crate::leanh::lean_dec_ref(v_a_2022_);
    crate::leanh::lean_dec(v_a_2021_);
    crate::leanh::lean_dec_ref(v_a_2020_);
    return v_res_2025_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHSubInt(
    mut v_e_2026_: *mut crate::leanh::LeanObject,
    mut v_a_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
    mut v_a_2029_: *mut crate::leanh::LeanObject,
    mut v_a_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2026_);
    v___x_2032_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_2026_, v_a_2028_);
    if crate::leanh::lean_obj_tag(v___x_2032_) == 0 {
        let mut v_a_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2034_: u8 = 0;
        v_a_2033_ = crate::leanh::lean_ctor_get(v___x_2032_, 0);
        crate::leanh::lean_inc(v_a_2033_);
        v___x_2034_ = (crate::leanh::lean_unbox(v_a_2033_) as u8);
        crate::leanh::lean_dec(v_a_2033_);
        if v___x_2034_ == 0 {
            let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2032_, 1);
            v___x_2035_ = l_Lean_Int_mkInstHSub;
            v___x_2036_ = l_Lean_Meta_isDefEqI(
                v_e_2026_,
                v___x_2035_,
                v_a_2027_,
                v_a_2028_,
                v_a_2029_,
                v_a_2030_,
            );
            return v___x_2036_;
        } else {
            crate::leanh::lean_dec_ref(v_e_2026_);
            return v___x_2032_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_2026_);
        return v___x_2032_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHSubInt___boxed(
    mut v_e_2037_: *mut crate::leanh::LeanObject,
    mut v_a_2038_: *mut crate::leanh::LeanObject,
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_a_2040_: *mut crate::leanh::LeanObject,
    mut v_a_2041_: *mut crate::leanh::LeanObject,
    mut v_a_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2043_ =
        l_Lean_Meta_DefEq_isInstHSubInt(v_e_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
    crate::leanh::lean_dec(v_a_2041_);
    crate::leanh::lean_dec_ref(v_a_2040_);
    crate::leanh::lean_dec(v_a_2039_);
    crate::leanh::lean_dec_ref(v_a_2038_);
    return v_res_2043_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstMulInt(
    mut v_e_2044_: *mut crate::leanh::LeanObject,
    mut v_a_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
    mut v_a_2047_: *mut crate::leanh::LeanObject,
    mut v_a_2048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2044_);
    v___x_2050_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_2044_, v_a_2046_);
    if crate::leanh::lean_obj_tag(v___x_2050_) == 0 {
        let mut v_a_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: u8 = 0;
        v_a_2051_ = crate::leanh::lean_ctor_get(v___x_2050_, 0);
        crate::leanh::lean_inc(v_a_2051_);
        v___x_2052_ = (crate::leanh::lean_unbox(v_a_2051_) as u8);
        crate::leanh::lean_dec(v_a_2051_);
        if v___x_2052_ == 0 {
            let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2050_, 1);
            v___x_2053_ = l_Lean_Int_mkInstMul;
            v___x_2054_ = l_Lean_Meta_isDefEqI(
                v_e_2044_,
                v___x_2053_,
                v_a_2045_,
                v_a_2046_,
                v_a_2047_,
                v_a_2048_,
            );
            return v___x_2054_;
        } else {
            crate::leanh::lean_dec_ref(v_e_2044_);
            return v___x_2050_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_2044_);
        return v___x_2050_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstMulInt___boxed(
    mut v_e_2055_: *mut crate::leanh::LeanObject,
    mut v_a_2056_: *mut crate::leanh::LeanObject,
    mut v_a_2057_: *mut crate::leanh::LeanObject,
    mut v_a_2058_: *mut crate::leanh::LeanObject,
    mut v_a_2059_: *mut crate::leanh::LeanObject,
    mut v_a_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2061_ =
        l_Lean_Meta_DefEq_isInstMulInt(v_e_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_);
    crate::leanh::lean_dec(v_a_2059_);
    crate::leanh::lean_dec_ref(v_a_2058_);
    crate::leanh::lean_dec(v_a_2057_);
    crate::leanh::lean_dec_ref(v_a_2056_);
    return v_res_2061_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHMulInt(
    mut v_e_2062_: *mut crate::leanh::LeanObject,
    mut v_a_2063_: *mut crate::leanh::LeanObject,
    mut v_a_2064_: *mut crate::leanh::LeanObject,
    mut v_a_2065_: *mut crate::leanh::LeanObject,
    mut v_a_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2062_);
    v___x_2068_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_2062_, v_a_2064_);
    if crate::leanh::lean_obj_tag(v___x_2068_) == 0 {
        let mut v_a_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2070_: u8 = 0;
        v_a_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
        crate::leanh::lean_inc(v_a_2069_);
        v___x_2070_ = (crate::leanh::lean_unbox(v_a_2069_) as u8);
        crate::leanh::lean_dec(v_a_2069_);
        if v___x_2070_ == 0 {
            let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2068_, 1);
            v___x_2071_ = l_Lean_Int_mkInstHMul;
            v___x_2072_ = l_Lean_Meta_isDefEqI(
                v_e_2062_,
                v___x_2071_,
                v_a_2063_,
                v_a_2064_,
                v_a_2065_,
                v_a_2066_,
            );
            return v___x_2072_;
        } else {
            crate::leanh::lean_dec_ref(v_e_2062_);
            return v___x_2068_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_2062_);
        return v___x_2068_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHMulInt___boxed(
    mut v_e_2073_: *mut crate::leanh::LeanObject,
    mut v_a_2074_: *mut crate::leanh::LeanObject,
    mut v_a_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_a_2078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ =
        l_Lean_Meta_DefEq_isInstHMulInt(v_e_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
    crate::leanh::lean_dec(v_a_2077_);
    crate::leanh::lean_dec_ref(v_a_2076_);
    crate::leanh::lean_dec(v_a_2075_);
    crate::leanh::lean_dec_ref(v_a_2074_);
    return v_res_2079_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLTInt(
    mut v_e_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
    mut v_a_2083_: *mut crate::leanh::LeanObject,
    mut v_a_2084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2080_);
    v___x_2086_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_2080_, v_a_2082_);
    if crate::leanh::lean_obj_tag(v___x_2086_) == 0 {
        let mut v_a_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2088_: u8 = 0;
        v_a_2087_ = crate::leanh::lean_ctor_get(v___x_2086_, 0);
        crate::leanh::lean_inc(v_a_2087_);
        v___x_2088_ = (crate::leanh::lean_unbox(v_a_2087_) as u8);
        crate::leanh::lean_dec(v_a_2087_);
        if v___x_2088_ == 0 {
            let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2086_, 1);
            v___x_2089_ = l_Lean_Int_mkInstLT;
            v___x_2090_ = l_Lean_Meta_isDefEqI(
                v_e_2080_,
                v___x_2089_,
                v_a_2081_,
                v_a_2082_,
                v_a_2083_,
                v_a_2084_,
            );
            return v___x_2090_;
        } else {
            crate::leanh::lean_dec_ref(v_e_2080_);
            return v___x_2086_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_2080_);
        return v___x_2086_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLTInt___boxed(
    mut v_e_2091_: *mut crate::leanh::LeanObject,
    mut v_a_2092_: *mut crate::leanh::LeanObject,
    mut v_a_2093_: *mut crate::leanh::LeanObject,
    mut v_a_2094_: *mut crate::leanh::LeanObject,
    mut v_a_2095_: *mut crate::leanh::LeanObject,
    mut v_a_2096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2097_ =
        l_Lean_Meta_DefEq_isInstLTInt(v_e_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
    crate::leanh::lean_dec(v_a_2095_);
    crate::leanh::lean_dec_ref(v_a_2094_);
    crate::leanh::lean_dec(v_a_2093_);
    crate::leanh::lean_dec_ref(v_a_2092_);
    return v_res_2097_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLEInt(
    mut v_e_2098_: *mut crate::leanh::LeanObject,
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2098_);
    v___x_2104_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_2098_, v_a_2100_);
    if crate::leanh::lean_obj_tag(v___x_2104_) == 0 {
        let mut v_a_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: u8 = 0;
        v_a_2105_ = crate::leanh::lean_ctor_get(v___x_2104_, 0);
        crate::leanh::lean_inc(v_a_2105_);
        v___x_2106_ = (crate::leanh::lean_unbox(v_a_2105_) as u8);
        crate::leanh::lean_dec(v_a_2105_);
        if v___x_2106_ == 0 {
            let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2104_, 1);
            v___x_2107_ = l_Lean_Int_mkInstLE;
            v___x_2108_ = l_Lean_Meta_isDefEqI(
                v_e_2098_,
                v___x_2107_,
                v_a_2099_,
                v_a_2100_,
                v_a_2101_,
                v_a_2102_,
            );
            return v___x_2108_;
        } else {
            crate::leanh::lean_dec_ref(v_e_2098_);
            return v___x_2104_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_2098_);
        return v___x_2104_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLEInt___boxed(
    mut v_e_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
    mut v_a_2111_: *mut crate::leanh::LeanObject,
    mut v_a_2112_: *mut crate::leanh::LeanObject,
    mut v_a_2113_: *mut crate::leanh::LeanObject,
    mut v_a_2114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2115_ =
        l_Lean_Meta_DefEq_isInstLEInt(v_e_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_);
    crate::leanh::lean_dec(v_a_2113_);
    crate::leanh::lean_dec_ref(v_a_2112_);
    crate::leanh::lean_dec(v_a_2111_);
    crate::leanh::lean_dec_ref(v_a_2110_);
    return v_res_2115_;
}
pub unsafe fn _init_l_Lean_Meta_DefEq_isInstDvdInt___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2116_ = crate::leanh::lean_box(0);
    v___x_2117_ = l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1;
    v___x_2118_ = l_Lean_mkConst(v___x_2117_, v___x_2116_);
    return v___x_2118_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstDvdInt(
    mut v_e_2119_: *mut crate::leanh::LeanObject,
    mut v_a_2120_: *mut crate::leanh::LeanObject,
    mut v_a_2121_: *mut crate::leanh::LeanObject,
    mut v_a_2122_: *mut crate::leanh::LeanObject,
    mut v_a_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2119_);
    v___x_2125_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_2119_, v_a_2121_);
    if crate::leanh::lean_obj_tag(v___x_2125_) == 0 {
        let mut v_a_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2127_: u8 = 0;
        v_a_2126_ = crate::leanh::lean_ctor_get(v___x_2125_, 0);
        crate::leanh::lean_inc(v_a_2126_);
        v___x_2127_ = (crate::leanh::lean_unbox(v_a_2126_) as u8);
        crate::leanh::lean_dec(v_a_2126_);
        if v___x_2127_ == 0 {
            let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_2125_, 1);
            v___x_2128_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_DefEq_isInstDvdInt___closed__0),
                core::ptr::addr_of_mut!(l_Lean_Meta_DefEq_isInstDvdInt___closed__0_once),
                _init_l_Lean_Meta_DefEq_isInstDvdInt___closed__0,
            );
            v___x_2129_ = l_Lean_Meta_isDefEqI(
                v_e_2119_,
                v___x_2128_,
                v_a_2120_,
                v_a_2121_,
                v_a_2122_,
                v_a_2123_,
            );
            return v___x_2129_;
        } else {
            crate::leanh::lean_dec_ref(v_e_2119_);
            return v___x_2125_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_e_2119_);
        return v___x_2125_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstDvdInt___boxed(
    mut v_e_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
    mut v_a_2133_: *mut crate::leanh::LeanObject,
    mut v_a_2134_: *mut crate::leanh::LeanObject,
    mut v_a_2135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2136_ =
        l_Lean_Meta_DefEq_isInstDvdInt(v_e_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
    crate::leanh::lean_dec(v_a_2134_);
    crate::leanh::lean_dec_ref(v_a_2133_);
    crate::leanh::lean_dec(v_a_2132_);
    crate::leanh::lean_dec_ref(v_a_2131_);
    return v_res_2136_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_IntInstTesters(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_IntInstTesters(
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
pub unsafe fn initialize_Lean_Meta_IntInstTesters(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_IntInstTesters(builtin);
}
