// Lean compiler output
// Module: Lean.Meta.NatInstTesters
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf, l_Lean_Nat_mkInstAdd, l_Lean_Nat_mkInstHAdd, l_Lean_Nat_mkInstHMul,
    l_Lean_Nat_mkInstLE, l_Lean_Nat_mkInstLT, l_Lean_Nat_mkInstMul,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_isDefEqI, runtime_initialize_Lean_Meta_Basic,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
};
pub static l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [105, 110, 115, 116, 79, 102, 78, 97, 116, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0_value)
                as *mut LeanObject,
            6887128300681693401 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 115, 116, 65, 100, 100, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0_value)
                as *mut LeanObject,
            13235980228967245028 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 115, 116, 83, 117, 98, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0_value)
                as *mut LeanObject,
            6649952479149719236 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [105, 110, 115, 116, 77, 117, 108, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0_value)
                as *mut LeanObject,
            6815769246081088251 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value: LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1_value)
                as *mut LeanObject,
            12263019034548362404 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstModNat___redArg___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Structural_isInstModNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstModNat___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstModNat___redArg___closed__0_value)
                as *mut LeanObject,
            6218646510627855613 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstModNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            105, 110, 115, 116, 78, 97, 116, 80, 111, 119, 78, 97, 116, 0,
        ],
    };
static mut l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0_value)
                as *mut LeanObject,
            9103900645098454167 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0_value)
                as *mut LeanObject,
            290288684272968877 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0],
    };
static mut l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0_value)
                as *mut LeanObject,
            9594062259507646949 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 83, 117, 98, 0],
    };
static mut l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0_value)
                as *mut LeanObject,
            10135981711945425184 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0],
    };
static mut l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0_value)
                as *mut LeanObject,
            18134279130838690737 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 68, 105, 118, 0],
    };
static mut l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0_value)
                as *mut LeanObject,
            1334142589224437282 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 77, 111, 100, 0],
    };
static mut l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0_value)
                as *mut LeanObject,
            6326466896415492082 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0_value: LeanStringObject<9> =
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
        m_data: [105, 110, 115, 116, 72, 80, 111, 119, 0],
    };
static mut l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0_value)
                as *mut LeanObject,
            14410956716278334933 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [105, 110, 115, 116, 76, 84, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0_value)
                as *mut LeanObject,
            14651840373392481165 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstLENat___redArg___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [105, 110, 115, 116, 76, 69, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Structural_isInstLENat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLENat___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstLENat___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLENat___redArg___closed__0_value)
                as *mut LeanObject,
            7582202872767459283 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstLENat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstLENat___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0_value)
                as *mut LeanObject,
            10480071703670411930 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatNat___redArg(
    mut v_e_945_: *mut LeanObject,
    mut v_a_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_952_: u8 = 0;
    let mut v___x_954_: u8 = 0;
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_966_: u8 = 0;
    let mut v_a_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_970_: u8 = 0;
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_948_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_945_, v_a_946_);
                if lean_obj_tag(v___x_948_) == 0 {
                    v_a_949_ = lean_ctor_get(v___x_948_, 0);
                    v_isSharedCheck_966_ = (!lean_is_exclusive(v___x_948_)) as u8;
                    if v_isSharedCheck_966_ == 0 {
                        v___x_951_ = v___x_948_;
                        v_isShared_952_ = v_isSharedCheck_966_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_949_);
                        lean_dec(v___x_948_);
                        v___x_951_ = lean_box(0);
                        v_isShared_952_ = v_isSharedCheck_966_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_967_ = lean_ctor_get(v___x_948_, 0);
                    v_isSharedCheck_974_ = (!lean_is_exclusive(v___x_948_)) as u8;
                    if v_isSharedCheck_974_ == 0 {
                        v___x_969_ = v___x_948_;
                        v_isShared_970_ = v_isSharedCheck_974_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_967_);
                        lean_dec(v___x_948_);
                        v___x_969_ = lean_box(0);
                        v_isShared_970_ = v_isSharedCheck_974_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_959_ = l_Lean_Expr_cleanupAnnotations(v_a_949_);
                v___x_960_ = l_Lean_Expr_isApp(v___x_959_);
                if v___x_960_ == 0 {
                    lean_dec_ref(v___x_959_);
                    state = 2;
                    continue;
                } else {
                    v___x_961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_959_);
                    v___x_962_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1;
                    v___x_963_ = l_Lean_Expr_isConstOf(v___x_961_, v___x_962_);
                    lean_dec_ref(v___x_961_);
                    if v___x_963_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_951_);
                        v___x_964_ = lean_box((v___x_963_) as usize);
                        v___x_965_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_965_, 0, v___x_964_);
                        return v___x_965_;
                    }
                }
            }
            2 => {
                v___x_954_ = 0;
                v___x_955_ = lean_box((v___x_954_) as usize);
                if v_isShared_952_ == 0 {
                    lean_ctor_set(v___x_951_, 0, v___x_955_);
                    v___x_957_ = v___x_951_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
                    v___x_957_ = v_reuseFailAlloc_958_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_957_;
            }
            4 => {
                if v_isShared_970_ == 0 {
                    v___x_972_ = v___x_969_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
                    v___x_972_ = v_reuseFailAlloc_973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_972_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatNat___redArg___boxed(
    mut v_e_975_: *mut LeanObject,
    mut v_a_976_: *mut LeanObject,
    mut v_a_977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_978_: *mut LeanObject = core::ptr::null_mut();
    v_res_978_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_e_975_, v_a_976_);
    lean_dec(v_a_976_);
    return v_res_978_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatNat(
    mut v_e_979_: *mut LeanObject,
    mut v_a_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
    mut v_a_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    v___x_985_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_e_979_, v_a_981_);
    return v___x_985_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstOfNatNat___boxed(
    mut v_e_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
    mut v_a_990_: *mut LeanObject,
    mut v_a_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_992_: *mut LeanObject = core::ptr::null_mut();
    v_res_992_ =
        l_Lean_Meta_Structural_isInstOfNatNat(v_e_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
    lean_dec(v_a_990_);
    lean_dec_ref(v_a_989_);
    lean_dec(v_a_988_);
    lean_dec_ref(v_a_987_);
    return v_res_992_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddNat___redArg(
    mut v_e_996_: *mut LeanObject,
    mut v_a_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut v_a_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_999_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_996_, v_a_997_);
                if lean_obj_tag(v___x_999_) == 0 {
                    v_a_1000_ = lean_ctor_get(v___x_999_, 0);
                    v_isSharedCheck_1011_ = (!lean_is_exclusive(v___x_999_)) as u8;
                    if v_isSharedCheck_1011_ == 0 {
                        v___x_1002_ = v___x_999_;
                        v_isShared_1003_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1000_);
                        lean_dec(v___x_999_);
                        v___x_1002_ = lean_box(0);
                        v_isShared_1003_ = v_isSharedCheck_1011_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1012_ = lean_ctor_get(v___x_999_, 0);
                    v_isSharedCheck_1019_ = (!lean_is_exclusive(v___x_999_)) as u8;
                    if v_isSharedCheck_1019_ == 0 {
                        v___x_1014_ = v___x_999_;
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1012_);
                        lean_dec(v___x_999_);
                        v___x_1014_ = lean_box(0);
                        v_isShared_1015_ = v_isSharedCheck_1019_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1004_ = l_Lean_Expr_cleanupAnnotations(v_a_1000_);
                v___x_1005_ = l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1;
                v___x_1006_ = l_Lean_Expr_isConstOf(v___x_1004_, v___x_1005_);
                lean_dec_ref(v___x_1004_);
                v___x_1007_ = lean_box((v___x_1006_) as usize);
                if v_isShared_1003_ == 0 {
                    lean_ctor_set(v___x_1002_, 0, v___x_1007_);
                    v___x_1009_ = v___x_1002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
                    v___x_1009_ = v_reuseFailAlloc_1010_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1009_;
            }
            3 => {
                if v_isShared_1015_ == 0 {
                    v___x_1017_ = v___x_1014_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
                    v___x_1017_ = v_reuseFailAlloc_1018_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddNat___redArg___boxed(
    mut v_e_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1023_: *mut LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_1020_, v_a_1021_);
    lean_dec(v_a_1021_);
    return v_res_1023_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddNat(
    mut v_e_1024_: *mut LeanObject,
    mut v_a_1025_: *mut LeanObject,
    mut v_a_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
    mut v_a_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    v___x_1030_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_1024_, v_a_1026_);
    return v___x_1030_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstAddNat___boxed(
    mut v_e_1031_: *mut LeanObject,
    mut v_a_1032_: *mut LeanObject,
    mut v_a_1033_: *mut LeanObject,
    mut v_a_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1037_: *mut LeanObject = core::ptr::null_mut();
    v_res_1037_ =
        l_Lean_Meta_Structural_isInstAddNat(v_e_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
    lean_dec(v_a_1035_);
    lean_dec_ref(v_a_1034_);
    lean_dec(v_a_1033_);
    lean_dec_ref(v_a_1032_);
    return v_res_1037_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubNat___redArg(
    mut v_e_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1048_: u8 = 0;
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: u8 = 0;
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut v_a_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1044_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1041_, v_a_1042_);
                if lean_obj_tag(v___x_1044_) == 0 {
                    v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
                    v_isSharedCheck_1056_ = (!lean_is_exclusive(v___x_1044_)) as u8;
                    if v_isSharedCheck_1056_ == 0 {
                        v___x_1047_ = v___x_1044_;
                        v_isShared_1048_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1045_);
                        lean_dec(v___x_1044_);
                        v___x_1047_ = lean_box(0);
                        v_isShared_1048_ = v_isSharedCheck_1056_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1057_ = lean_ctor_get(v___x_1044_, 0);
                    v_isSharedCheck_1064_ = (!lean_is_exclusive(v___x_1044_)) as u8;
                    if v_isSharedCheck_1064_ == 0 {
                        v___x_1059_ = v___x_1044_;
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1057_);
                        lean_dec(v___x_1044_);
                        v___x_1059_ = lean_box(0);
                        v_isShared_1060_ = v_isSharedCheck_1064_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1049_ = l_Lean_Expr_cleanupAnnotations(v_a_1045_);
                v___x_1050_ = l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1;
                v___x_1051_ = l_Lean_Expr_isConstOf(v___x_1049_, v___x_1050_);
                lean_dec_ref(v___x_1049_);
                v___x_1052_ = lean_box((v___x_1051_) as usize);
                if v_isShared_1048_ == 0 {
                    lean_ctor_set(v___x_1047_, 0, v___x_1052_);
                    v___x_1054_ = v___x_1047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
                    v___x_1054_ = v_reuseFailAlloc_1055_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1054_;
            }
            3 => {
                if v_isShared_1060_ == 0 {
                    v___x_1062_ = v___x_1059_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
                    v___x_1062_ = v_reuseFailAlloc_1063_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubNat___redArg___boxed(
    mut v_e_1065_: *mut LeanObject,
    mut v_a_1066_: *mut LeanObject,
    mut v_a_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_e_1065_, v_a_1066_);
    lean_dec(v_a_1066_);
    return v_res_1068_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubNat(
    mut v_e_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    v___x_1075_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_e_1069_, v_a_1071_);
    return v___x_1075_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstSubNat___boxed(
    mut v_e_1076_: *mut LeanObject,
    mut v_a_1077_: *mut LeanObject,
    mut v_a_1078_: *mut LeanObject,
    mut v_a_1079_: *mut LeanObject,
    mut v_a_1080_: *mut LeanObject,
    mut v_a_1081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1082_: *mut LeanObject = core::ptr::null_mut();
    v_res_1082_ =
        l_Lean_Meta_Structural_isInstSubNat(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
    lean_dec(v_a_1080_);
    lean_dec_ref(v_a_1079_);
    lean_dec(v_a_1078_);
    lean_dec_ref(v_a_1077_);
    return v_res_1082_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulNat___redArg(
    mut v_e_1086_: *mut LeanObject,
    mut v_a_1087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1093_: u8 = 0;
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: u8 = 0;
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut v_a_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1109_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1089_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1086_, v_a_1087_);
                if lean_obj_tag(v___x_1089_) == 0 {
                    v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
                    v_isSharedCheck_1101_ = (!lean_is_exclusive(v___x_1089_)) as u8;
                    if v_isSharedCheck_1101_ == 0 {
                        v___x_1092_ = v___x_1089_;
                        v_isShared_1093_ = v_isSharedCheck_1101_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1090_);
                        lean_dec(v___x_1089_);
                        v___x_1092_ = lean_box(0);
                        v_isShared_1093_ = v_isSharedCheck_1101_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1102_ = lean_ctor_get(v___x_1089_, 0);
                    v_isSharedCheck_1109_ = (!lean_is_exclusive(v___x_1089_)) as u8;
                    if v_isSharedCheck_1109_ == 0 {
                        v___x_1104_ = v___x_1089_;
                        v_isShared_1105_ = v_isSharedCheck_1109_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1102_);
                        lean_dec(v___x_1089_);
                        v___x_1104_ = lean_box(0);
                        v_isShared_1105_ = v_isSharedCheck_1109_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1094_ = l_Lean_Expr_cleanupAnnotations(v_a_1090_);
                v___x_1095_ = l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1;
                v___x_1096_ = l_Lean_Expr_isConstOf(v___x_1094_, v___x_1095_);
                lean_dec_ref(v___x_1094_);
                v___x_1097_ = lean_box((v___x_1096_) as usize);
                if v_isShared_1093_ == 0 {
                    lean_ctor_set(v___x_1092_, 0, v___x_1097_);
                    v___x_1099_ = v___x_1092_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
                    v___x_1099_ = v_reuseFailAlloc_1100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1099_;
            }
            3 => {
                if v_isShared_1105_ == 0 {
                    v___x_1107_ = v___x_1104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
                    v___x_1107_ = v_reuseFailAlloc_1108_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulNat___redArg___boxed(
    mut v_e_1110_: *mut LeanObject,
    mut v_a_1111_: *mut LeanObject,
    mut v_a_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1113_: *mut LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_1110_, v_a_1111_);
    lean_dec(v_a_1111_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulNat(
    mut v_e_1114_: *mut LeanObject,
    mut v_a_1115_: *mut LeanObject,
    mut v_a_1116_: *mut LeanObject,
    mut v_a_1117_: *mut LeanObject,
    mut v_a_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_1114_, v_a_1116_);
    return v___x_1120_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstMulNat___boxed(
    mut v_e_1121_: *mut LeanObject,
    mut v_a_1122_: *mut LeanObject,
    mut v_a_1123_: *mut LeanObject,
    mut v_a_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
    mut v_a_1126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1127_: *mut LeanObject = core::ptr::null_mut();
    v_res_1127_ =
        l_Lean_Meta_Structural_isInstMulNat(v_e_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
    lean_dec(v_a_1125_);
    lean_dec_ref(v_a_1124_);
    lean_dec(v_a_1123_);
    lean_dec_ref(v_a_1122_);
    return v_res_1127_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivNat___redArg(
    mut v_e_1133_: *mut LeanObject,
    mut v_a_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: u8 = 0;
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1148_: u8 = 0;
    let mut v_a_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1152_: u8 = 0;
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1136_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1133_, v_a_1134_);
                if lean_obj_tag(v___x_1136_) == 0 {
                    v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
                    v_isSharedCheck_1148_ = (!lean_is_exclusive(v___x_1136_)) as u8;
                    if v_isSharedCheck_1148_ == 0 {
                        v___x_1139_ = v___x_1136_;
                        v_isShared_1140_ = v_isSharedCheck_1148_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1137_);
                        lean_dec(v___x_1136_);
                        v___x_1139_ = lean_box(0);
                        v_isShared_1140_ = v_isSharedCheck_1148_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1149_ = lean_ctor_get(v___x_1136_, 0);
                    v_isSharedCheck_1156_ = (!lean_is_exclusive(v___x_1136_)) as u8;
                    if v_isSharedCheck_1156_ == 0 {
                        v___x_1151_ = v___x_1136_;
                        v_isShared_1152_ = v_isSharedCheck_1156_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1149_);
                        lean_dec(v___x_1136_);
                        v___x_1151_ = lean_box(0);
                        v_isShared_1152_ = v_isSharedCheck_1156_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1141_ = l_Lean_Expr_cleanupAnnotations(v_a_1137_);
                v___x_1142_ = l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2;
                v___x_1143_ = l_Lean_Expr_isConstOf(v___x_1141_, v___x_1142_);
                lean_dec_ref(v___x_1141_);
                v___x_1144_ = lean_box((v___x_1143_) as usize);
                if v_isShared_1140_ == 0 {
                    lean_ctor_set(v___x_1139_, 0, v___x_1144_);
                    v___x_1146_ = v___x_1139_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
                    v___x_1146_ = v_reuseFailAlloc_1147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1146_;
            }
            3 => {
                if v_isShared_1152_ == 0 {
                    v___x_1154_ = v___x_1151_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
                    v___x_1154_ = v_reuseFailAlloc_1155_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivNat___redArg___boxed(
    mut v_e_1157_: *mut LeanObject,
    mut v_a_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1160_: *mut LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_e_1157_, v_a_1158_);
    lean_dec(v_a_1158_);
    return v_res_1160_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivNat(
    mut v_e_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
    mut v_a_1163_: *mut LeanObject,
    mut v_a_1164_: *mut LeanObject,
    mut v_a_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    v___x_1167_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_e_1161_, v_a_1163_);
    return v___x_1167_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDivNat___boxed(
    mut v_e_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
    mut v_a_1170_: *mut LeanObject,
    mut v_a_1171_: *mut LeanObject,
    mut v_a_1172_: *mut LeanObject,
    mut v_a_1173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1174_: *mut LeanObject = core::ptr::null_mut();
    v_res_1174_ =
        l_Lean_Meta_Structural_isInstDivNat(v_e_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
    lean_dec(v_a_1172_);
    lean_dec_ref(v_a_1171_);
    lean_dec(v_a_1170_);
    lean_dec_ref(v_a_1169_);
    return v_res_1174_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstModNat___redArg(
    mut v_e_1179_: *mut LeanObject,
    mut v_a_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1186_: u8 = 0;
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: u8 = 0;
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1194_: u8 = 0;
    let mut v_a_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1182_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1179_, v_a_1180_);
                if lean_obj_tag(v___x_1182_) == 0 {
                    v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
                    v_isSharedCheck_1194_ = (!lean_is_exclusive(v___x_1182_)) as u8;
                    if v_isSharedCheck_1194_ == 0 {
                        v___x_1185_ = v___x_1182_;
                        v_isShared_1186_ = v_isSharedCheck_1194_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1183_);
                        lean_dec(v___x_1182_);
                        v___x_1185_ = lean_box(0);
                        v_isShared_1186_ = v_isSharedCheck_1194_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1195_ = lean_ctor_get(v___x_1182_, 0);
                    v_isSharedCheck_1202_ = (!lean_is_exclusive(v___x_1182_)) as u8;
                    if v_isSharedCheck_1202_ == 0 {
                        v___x_1197_ = v___x_1182_;
                        v_isShared_1198_ = v_isSharedCheck_1202_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1195_);
                        lean_dec(v___x_1182_);
                        v___x_1197_ = lean_box(0);
                        v_isShared_1198_ = v_isSharedCheck_1202_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1187_ = l_Lean_Expr_cleanupAnnotations(v_a_1183_);
                v___x_1188_ = l_Lean_Meta_Structural_isInstModNat___redArg___closed__1;
                v___x_1189_ = l_Lean_Expr_isConstOf(v___x_1187_, v___x_1188_);
                lean_dec_ref(v___x_1187_);
                v___x_1190_ = lean_box((v___x_1189_) as usize);
                if v_isShared_1186_ == 0 {
                    lean_ctor_set(v___x_1185_, 0, v___x_1190_);
                    v___x_1192_ = v___x_1185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
                    v___x_1192_ = v_reuseFailAlloc_1193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1192_;
            }
            3 => {
                if v_isShared_1198_ == 0 {
                    v___x_1200_ = v___x_1197_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
                    v___x_1200_ = v_reuseFailAlloc_1201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstModNat___redArg___boxed(
    mut v_e_1203_: *mut LeanObject,
    mut v_a_1204_: *mut LeanObject,
    mut v_a_1205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1206_: *mut LeanObject = core::ptr::null_mut();
    v_res_1206_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_e_1203_, v_a_1204_);
    lean_dec(v_a_1204_);
    return v_res_1206_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstModNat(
    mut v_e_1207_: *mut LeanObject,
    mut v_a_1208_: *mut LeanObject,
    mut v_a_1209_: *mut LeanObject,
    mut v_a_1210_: *mut LeanObject,
    mut v_a_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_e_1207_, v_a_1209_);
    return v___x_1213_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstModNat___boxed(
    mut v_e_1214_: *mut LeanObject,
    mut v_a_1215_: *mut LeanObject,
    mut v_a_1216_: *mut LeanObject,
    mut v_a_1217_: *mut LeanObject,
    mut v_a_1218_: *mut LeanObject,
    mut v_a_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1220_: *mut LeanObject = core::ptr::null_mut();
    v_res_1220_ =
        l_Lean_Meta_Structural_isInstModNat(v_e_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
    lean_dec(v_a_1218_);
    lean_dec_ref(v_a_1217_);
    lean_dec(v_a_1216_);
    lean_dec_ref(v_a_1215_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowNat___redArg(
    mut v_e_1224_: *mut LeanObject,
    mut v_a_1225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: u8 = 0;
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1239_: u8 = 0;
    let mut v_a_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1243_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1227_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1224_, v_a_1225_);
                if lean_obj_tag(v___x_1227_) == 0 {
                    v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
                    v_isSharedCheck_1239_ = (!lean_is_exclusive(v___x_1227_)) as u8;
                    if v_isSharedCheck_1239_ == 0 {
                        v___x_1230_ = v___x_1227_;
                        v_isShared_1231_ = v_isSharedCheck_1239_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1228_);
                        lean_dec(v___x_1227_);
                        v___x_1230_ = lean_box(0);
                        v_isShared_1231_ = v_isSharedCheck_1239_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1240_ = lean_ctor_get(v___x_1227_, 0);
                    v_isSharedCheck_1247_ = (!lean_is_exclusive(v___x_1227_)) as u8;
                    if v_isSharedCheck_1247_ == 0 {
                        v___x_1242_ = v___x_1227_;
                        v_isShared_1243_ = v_isSharedCheck_1247_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1240_);
                        lean_dec(v___x_1227_);
                        v___x_1242_ = lean_box(0);
                        v_isShared_1243_ = v_isSharedCheck_1247_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1232_ = l_Lean_Expr_cleanupAnnotations(v_a_1228_);
                v___x_1233_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1;
                v___x_1234_ = l_Lean_Expr_isConstOf(v___x_1232_, v___x_1233_);
                lean_dec_ref(v___x_1232_);
                v___x_1235_ = lean_box((v___x_1234_) as usize);
                if v_isShared_1231_ == 0 {
                    lean_ctor_set(v___x_1230_, 0, v___x_1235_);
                    v___x_1237_ = v___x_1230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
                    v___x_1237_ = v_reuseFailAlloc_1238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1237_;
            }
            3 => {
                if v_isShared_1243_ == 0 {
                    v___x_1245_ = v___x_1242_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
                    v___x_1245_ = v_reuseFailAlloc_1246_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowNat___redArg___boxed(
    mut v_e_1248_: *mut LeanObject,
    mut v_a_1249_: *mut LeanObject,
    mut v_a_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_e_1248_, v_a_1249_);
    lean_dec(v_a_1249_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowNat(
    mut v_e_1252_: *mut LeanObject,
    mut v_a_1253_: *mut LeanObject,
    mut v_a_1254_: *mut LeanObject,
    mut v_a_1255_: *mut LeanObject,
    mut v_a_1256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    v___x_1258_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_e_1252_, v_a_1254_);
    return v___x_1258_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstNatPowNat___boxed(
    mut v_e_1259_: *mut LeanObject,
    mut v_a_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
    mut v_a_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1265_: *mut LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_Meta_Structural_isInstNatPowNat(
        v_e_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_,
    );
    lean_dec(v_a_1263_);
    lean_dec_ref(v_a_1262_);
    lean_dec(v_a_1261_);
    lean_dec_ref(v_a_1260_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowNat___redArg(
    mut v_e_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1278_: u8 = 0;
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: u8 = 0;
    let mut v_arg_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: u8 = 0;
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: u8 = 0;
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1292_: u8 = 0;
    let mut v_a_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1296_: u8 = 0;
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1272_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1269_, v_a_1270_);
                if lean_obj_tag(v___x_1272_) == 0 {
                    v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
                    v_isSharedCheck_1292_ = (!lean_is_exclusive(v___x_1272_)) as u8;
                    if v_isSharedCheck_1292_ == 0 {
                        v___x_1275_ = v___x_1272_;
                        v_isShared_1276_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1273_);
                        lean_dec(v___x_1272_);
                        v___x_1275_ = lean_box(0);
                        v_isShared_1276_ = v_isSharedCheck_1292_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1293_ = lean_ctor_get(v___x_1272_, 0);
                    v_isSharedCheck_1300_ = (!lean_is_exclusive(v___x_1272_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v___x_1295_ = v___x_1272_;
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1293_);
                        lean_dec(v___x_1272_);
                        v___x_1295_ = lean_box(0);
                        v_isShared_1296_ = v_isSharedCheck_1300_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1283_ = l_Lean_Expr_cleanupAnnotations(v_a_1273_);
                v___x_1284_ = l_Lean_Expr_isApp(v___x_1283_);
                if v___x_1284_ == 0 {
                    lean_dec_ref(v___x_1283_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1285_ = lean_ctor_get(v___x_1283_, 1);
                    lean_inc_ref(v_arg_1285_);
                    v___x_1286_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1283_);
                    v___x_1287_ = l_Lean_Expr_isApp(v___x_1286_);
                    if v___x_1287_ == 0 {
                        lean_dec_ref(v___x_1286_);
                        lean_dec_ref(v_arg_1285_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1288_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1286_);
                        v___x_1289_ = l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1;
                        v___x_1290_ = l_Lean_Expr_isConstOf(v___x_1288_, v___x_1289_);
                        lean_dec_ref(v___x_1288_);
                        if v___x_1290_ == 0 {
                            lean_dec_ref(v_arg_1285_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_1275_);
                            v___x_1291_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(
                                v_arg_1285_,
                                v_a_1270_,
                            );
                            return v___x_1291_;
                        }
                    }
                }
            }
            2 => {
                v___x_1278_ = 0;
                v___x_1279_ = lean_box((v___x_1278_) as usize);
                if v_isShared_1276_ == 0 {
                    lean_ctor_set(v___x_1275_, 0, v___x_1279_);
                    v___x_1281_ = v___x_1275_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1279_);
                    v___x_1281_ = v_reuseFailAlloc_1282_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1281_;
            }
            4 => {
                if v_isShared_1296_ == 0 {
                    v___x_1298_ = v___x_1295_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
                    v___x_1298_ = v_reuseFailAlloc_1299_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowNat___redArg___boxed(
    mut v_e_1301_: *mut LeanObject,
    mut v_a_1302_: *mut LeanObject,
    mut v_a_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1304_: *mut LeanObject = core::ptr::null_mut();
    v_res_1304_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_1301_, v_a_1302_);
    lean_dec(v_a_1302_);
    return v_res_1304_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowNat(
    mut v_e_1305_: *mut LeanObject,
    mut v_a_1306_: *mut LeanObject,
    mut v_a_1307_: *mut LeanObject,
    mut v_a_1308_: *mut LeanObject,
    mut v_a_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    v___x_1311_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_1305_, v_a_1307_);
    return v___x_1311_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstPowNat___boxed(
    mut v_e_1312_: *mut LeanObject,
    mut v_a_1313_: *mut LeanObject,
    mut v_a_1314_: *mut LeanObject,
    mut v_a_1315_: *mut LeanObject,
    mut v_a_1316_: *mut LeanObject,
    mut v_a_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1318_: *mut LeanObject = core::ptr::null_mut();
    v_res_1318_ =
        l_Lean_Meta_Structural_isInstPowNat(v_e_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
    lean_dec(v_a_1316_);
    lean_dec_ref(v_a_1315_);
    lean_dec(v_a_1314_);
    lean_dec_ref(v_a_1313_);
    return v_res_1318_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddNat___redArg(
    mut v_e_1322_: *mut LeanObject,
    mut v_a_1323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1329_: u8 = 0;
    let mut v___x_1331_: u8 = 0;
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v_arg_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_a_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1325_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1322_, v_a_1323_);
                if lean_obj_tag(v___x_1325_) == 0 {
                    v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1345_ = (!lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1345_ == 0 {
                        v___x_1328_ = v___x_1325_;
                        v_isShared_1329_ = v_isSharedCheck_1345_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1326_);
                        lean_dec(v___x_1325_);
                        v___x_1328_ = lean_box(0);
                        v_isShared_1329_ = v_isSharedCheck_1345_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1346_ = lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1353_ = (!lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1353_ == 0 {
                        v___x_1348_ = v___x_1325_;
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1346_);
                        lean_dec(v___x_1325_);
                        v___x_1348_ = lean_box(0);
                        v_isShared_1349_ = v_isSharedCheck_1353_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1336_ = l_Lean_Expr_cleanupAnnotations(v_a_1326_);
                v___x_1337_ = l_Lean_Expr_isApp(v___x_1336_);
                if v___x_1337_ == 0 {
                    lean_dec_ref(v___x_1336_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1338_ = lean_ctor_get(v___x_1336_, 1);
                    lean_inc_ref(v_arg_1338_);
                    v___x_1339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1336_);
                    v___x_1340_ = l_Lean_Expr_isApp(v___x_1339_);
                    if v___x_1340_ == 0 {
                        lean_dec_ref(v___x_1339_);
                        lean_dec_ref(v_arg_1338_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1339_);
                        v___x_1342_ = l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1;
                        v___x_1343_ = l_Lean_Expr_isConstOf(v___x_1341_, v___x_1342_);
                        lean_dec_ref(v___x_1341_);
                        if v___x_1343_ == 0 {
                            lean_dec_ref(v_arg_1338_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_1328_);
                            v___x_1344_ = l_Lean_Meta_Structural_isInstAddNat___redArg(
                                v_arg_1338_,
                                v_a_1323_,
                            );
                            return v___x_1344_;
                        }
                    }
                }
            }
            2 => {
                v___x_1331_ = 0;
                v___x_1332_ = lean_box((v___x_1331_) as usize);
                if v_isShared_1329_ == 0 {
                    lean_ctor_set(v___x_1328_, 0, v___x_1332_);
                    v___x_1334_ = v___x_1328_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
                    v___x_1334_ = v_reuseFailAlloc_1335_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1334_;
            }
            4 => {
                if v_isShared_1349_ == 0 {
                    v___x_1351_ = v___x_1348_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
                    v___x_1351_ = v_reuseFailAlloc_1352_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddNat___redArg___boxed(
    mut v_e_1354_: *mut LeanObject,
    mut v_a_1355_: *mut LeanObject,
    mut v_a_1356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1357_: *mut LeanObject = core::ptr::null_mut();
    v_res_1357_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_1354_, v_a_1355_);
    lean_dec(v_a_1355_);
    return v_res_1357_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddNat(
    mut v_e_1358_: *mut LeanObject,
    mut v_a_1359_: *mut LeanObject,
    mut v_a_1360_: *mut LeanObject,
    mut v_a_1361_: *mut LeanObject,
    mut v_a_1362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1364_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_1358_, v_a_1360_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHAddNat___boxed(
    mut v_e_1365_: *mut LeanObject,
    mut v_a_1366_: *mut LeanObject,
    mut v_a_1367_: *mut LeanObject,
    mut v_a_1368_: *mut LeanObject,
    mut v_a_1369_: *mut LeanObject,
    mut v_a_1370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1371_: *mut LeanObject = core::ptr::null_mut();
    v_res_1371_ =
        l_Lean_Meta_Structural_isInstHAddNat(v_e_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
    lean_dec(v_a_1369_);
    lean_dec_ref(v_a_1368_);
    lean_dec(v_a_1367_);
    lean_dec_ref(v_a_1366_);
    return v_res_1371_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubNat___redArg(
    mut v_e_1375_: *mut LeanObject,
    mut v_a_1376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1382_: u8 = 0;
    let mut v___x_1384_: u8 = 0;
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut v_arg_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: u8 = 0;
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: u8 = 0;
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_a_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1402_: u8 = 0;
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1378_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1375_, v_a_1376_);
                if lean_obj_tag(v___x_1378_) == 0 {
                    v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
                    v_isSharedCheck_1398_ = (!lean_is_exclusive(v___x_1378_)) as u8;
                    if v_isSharedCheck_1398_ == 0 {
                        v___x_1381_ = v___x_1378_;
                        v_isShared_1382_ = v_isSharedCheck_1398_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1379_);
                        lean_dec(v___x_1378_);
                        v___x_1381_ = lean_box(0);
                        v_isShared_1382_ = v_isSharedCheck_1398_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1399_ = lean_ctor_get(v___x_1378_, 0);
                    v_isSharedCheck_1406_ = (!lean_is_exclusive(v___x_1378_)) as u8;
                    if v_isSharedCheck_1406_ == 0 {
                        v___x_1401_ = v___x_1378_;
                        v_isShared_1402_ = v_isSharedCheck_1406_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1399_);
                        lean_dec(v___x_1378_);
                        v___x_1401_ = lean_box(0);
                        v_isShared_1402_ = v_isSharedCheck_1406_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1389_ = l_Lean_Expr_cleanupAnnotations(v_a_1379_);
                v___x_1390_ = l_Lean_Expr_isApp(v___x_1389_);
                if v___x_1390_ == 0 {
                    lean_dec_ref(v___x_1389_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1391_ = lean_ctor_get(v___x_1389_, 1);
                    lean_inc_ref(v_arg_1391_);
                    v___x_1392_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1389_);
                    v___x_1393_ = l_Lean_Expr_isApp(v___x_1392_);
                    if v___x_1393_ == 0 {
                        lean_dec_ref(v___x_1392_);
                        lean_dec_ref(v_arg_1391_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1394_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1392_);
                        v___x_1395_ = l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1;
                        v___x_1396_ = l_Lean_Expr_isConstOf(v___x_1394_, v___x_1395_);
                        lean_dec_ref(v___x_1394_);
                        if v___x_1396_ == 0 {
                            lean_dec_ref(v_arg_1391_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_1381_);
                            v___x_1397_ = l_Lean_Meta_Structural_isInstSubNat___redArg(
                                v_arg_1391_,
                                v_a_1376_,
                            );
                            return v___x_1397_;
                        }
                    }
                }
            }
            2 => {
                v___x_1384_ = 0;
                v___x_1385_ = lean_box((v___x_1384_) as usize);
                if v_isShared_1382_ == 0 {
                    lean_ctor_set(v___x_1381_, 0, v___x_1385_);
                    v___x_1387_ = v___x_1381_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
                    v___x_1387_ = v_reuseFailAlloc_1388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1387_;
            }
            4 => {
                if v_isShared_1402_ == 0 {
                    v___x_1404_ = v___x_1401_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1404_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubNat___redArg___boxed(
    mut v_e_1407_: *mut LeanObject,
    mut v_a_1408_: *mut LeanObject,
    mut v_a_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1410_: *mut LeanObject = core::ptr::null_mut();
    v_res_1410_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_1407_, v_a_1408_);
    lean_dec(v_a_1408_);
    return v_res_1410_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubNat(
    mut v_e_1411_: *mut LeanObject,
    mut v_a_1412_: *mut LeanObject,
    mut v_a_1413_: *mut LeanObject,
    mut v_a_1414_: *mut LeanObject,
    mut v_a_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_1411_, v_a_1413_);
    return v___x_1417_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHSubNat___boxed(
    mut v_e_1418_: *mut LeanObject,
    mut v_a_1419_: *mut LeanObject,
    mut v_a_1420_: *mut LeanObject,
    mut v_a_1421_: *mut LeanObject,
    mut v_a_1422_: *mut LeanObject,
    mut v_a_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1424_: *mut LeanObject = core::ptr::null_mut();
    v_res_1424_ =
        l_Lean_Meta_Structural_isInstHSubNat(v_e_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
    lean_dec(v_a_1422_);
    lean_dec_ref(v_a_1421_);
    lean_dec(v_a_1420_);
    lean_dec_ref(v_a_1419_);
    return v_res_1424_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulNat___redArg(
    mut v_e_1428_: *mut LeanObject,
    mut v_a_1429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1435_: u8 = 0;
    let mut v___x_1437_: u8 = 0;
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u8 = 0;
    let mut v_arg_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1451_: u8 = 0;
    let mut v_a_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1455_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1431_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1428_, v_a_1429_);
                if lean_obj_tag(v___x_1431_) == 0 {
                    v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
                    v_isSharedCheck_1451_ = (!lean_is_exclusive(v___x_1431_)) as u8;
                    if v_isSharedCheck_1451_ == 0 {
                        v___x_1434_ = v___x_1431_;
                        v_isShared_1435_ = v_isSharedCheck_1451_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1432_);
                        lean_dec(v___x_1431_);
                        v___x_1434_ = lean_box(0);
                        v_isShared_1435_ = v_isSharedCheck_1451_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1452_ = lean_ctor_get(v___x_1431_, 0);
                    v_isSharedCheck_1459_ = (!lean_is_exclusive(v___x_1431_)) as u8;
                    if v_isSharedCheck_1459_ == 0 {
                        v___x_1454_ = v___x_1431_;
                        v_isShared_1455_ = v_isSharedCheck_1459_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1452_);
                        lean_dec(v___x_1431_);
                        v___x_1454_ = lean_box(0);
                        v_isShared_1455_ = v_isSharedCheck_1459_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1442_ = l_Lean_Expr_cleanupAnnotations(v_a_1432_);
                v___x_1443_ = l_Lean_Expr_isApp(v___x_1442_);
                if v___x_1443_ == 0 {
                    lean_dec_ref(v___x_1442_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1444_ = lean_ctor_get(v___x_1442_, 1);
                    lean_inc_ref(v_arg_1444_);
                    v___x_1445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1442_);
                    v___x_1446_ = l_Lean_Expr_isApp(v___x_1445_);
                    if v___x_1446_ == 0 {
                        lean_dec_ref(v___x_1445_);
                        lean_dec_ref(v_arg_1444_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1445_);
                        v___x_1448_ = l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1;
                        v___x_1449_ = l_Lean_Expr_isConstOf(v___x_1447_, v___x_1448_);
                        lean_dec_ref(v___x_1447_);
                        if v___x_1449_ == 0 {
                            lean_dec_ref(v_arg_1444_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_1434_);
                            v___x_1450_ = l_Lean_Meta_Structural_isInstMulNat___redArg(
                                v_arg_1444_,
                                v_a_1429_,
                            );
                            return v___x_1450_;
                        }
                    }
                }
            }
            2 => {
                v___x_1437_ = 0;
                v___x_1438_ = lean_box((v___x_1437_) as usize);
                if v_isShared_1435_ == 0 {
                    lean_ctor_set(v___x_1434_, 0, v___x_1438_);
                    v___x_1440_ = v___x_1434_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
                    v___x_1440_ = v_reuseFailAlloc_1441_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1440_;
            }
            4 => {
                if v_isShared_1455_ == 0 {
                    v___x_1457_ = v___x_1454_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1452_);
                    v___x_1457_ = v_reuseFailAlloc_1458_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulNat___redArg___boxed(
    mut v_e_1460_: *mut LeanObject,
    mut v_a_1461_: *mut LeanObject,
    mut v_a_1462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1463_: *mut LeanObject = core::ptr::null_mut();
    v_res_1463_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_1460_, v_a_1461_);
    lean_dec(v_a_1461_);
    return v_res_1463_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulNat(
    mut v_e_1464_: *mut LeanObject,
    mut v_a_1465_: *mut LeanObject,
    mut v_a_1466_: *mut LeanObject,
    mut v_a_1467_: *mut LeanObject,
    mut v_a_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    v___x_1470_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_1464_, v_a_1466_);
    return v___x_1470_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHMulNat___boxed(
    mut v_e_1471_: *mut LeanObject,
    mut v_a_1472_: *mut LeanObject,
    mut v_a_1473_: *mut LeanObject,
    mut v_a_1474_: *mut LeanObject,
    mut v_a_1475_: *mut LeanObject,
    mut v_a_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1477_: *mut LeanObject = core::ptr::null_mut();
    v_res_1477_ =
        l_Lean_Meta_Structural_isInstHMulNat(v_e_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_);
    lean_dec(v_a_1475_);
    lean_dec_ref(v_a_1474_);
    lean_dec(v_a_1473_);
    lean_dec_ref(v_a_1472_);
    return v_res_1477_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivNat___redArg(
    mut v_e_1481_: *mut LeanObject,
    mut v_a_1482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v___x_1490_: u8 = 0;
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: u8 = 0;
    let mut v_arg_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1504_: u8 = 0;
    let mut v_a_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1508_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1484_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1481_, v_a_1482_);
                if lean_obj_tag(v___x_1484_) == 0 {
                    v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
                    v_isSharedCheck_1504_ = (!lean_is_exclusive(v___x_1484_)) as u8;
                    if v_isSharedCheck_1504_ == 0 {
                        v___x_1487_ = v___x_1484_;
                        v_isShared_1488_ = v_isSharedCheck_1504_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1485_);
                        lean_dec(v___x_1484_);
                        v___x_1487_ = lean_box(0);
                        v_isShared_1488_ = v_isSharedCheck_1504_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1505_ = lean_ctor_get(v___x_1484_, 0);
                    v_isSharedCheck_1512_ = (!lean_is_exclusive(v___x_1484_)) as u8;
                    if v_isSharedCheck_1512_ == 0 {
                        v___x_1507_ = v___x_1484_;
                        v_isShared_1508_ = v_isSharedCheck_1512_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1505_);
                        lean_dec(v___x_1484_);
                        v___x_1507_ = lean_box(0);
                        v_isShared_1508_ = v_isSharedCheck_1512_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1495_ = l_Lean_Expr_cleanupAnnotations(v_a_1485_);
                v___x_1496_ = l_Lean_Expr_isApp(v___x_1495_);
                if v___x_1496_ == 0 {
                    lean_dec_ref(v___x_1495_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1497_ = lean_ctor_get(v___x_1495_, 1);
                    lean_inc_ref(v_arg_1497_);
                    v___x_1498_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1495_);
                    v___x_1499_ = l_Lean_Expr_isApp(v___x_1498_);
                    if v___x_1499_ == 0 {
                        lean_dec_ref(v___x_1498_);
                        lean_dec_ref(v_arg_1497_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1500_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1498_);
                        v___x_1501_ = l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1;
                        v___x_1502_ = l_Lean_Expr_isConstOf(v___x_1500_, v___x_1501_);
                        lean_dec_ref(v___x_1500_);
                        if v___x_1502_ == 0 {
                            lean_dec_ref(v_arg_1497_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_1487_);
                            v___x_1503_ = l_Lean_Meta_Structural_isInstDivNat___redArg(
                                v_arg_1497_,
                                v_a_1482_,
                            );
                            return v___x_1503_;
                        }
                    }
                }
            }
            2 => {
                v___x_1490_ = 0;
                v___x_1491_ = lean_box((v___x_1490_) as usize);
                if v_isShared_1488_ == 0 {
                    lean_ctor_set(v___x_1487_, 0, v___x_1491_);
                    v___x_1493_ = v___x_1487_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1491_);
                    v___x_1493_ = v_reuseFailAlloc_1494_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1493_;
            }
            4 => {
                if v_isShared_1508_ == 0 {
                    v___x_1510_ = v___x_1507_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
                    v___x_1510_ = v_reuseFailAlloc_1511_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivNat___redArg___boxed(
    mut v_e_1513_: *mut LeanObject,
    mut v_a_1514_: *mut LeanObject,
    mut v_a_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1516_: *mut LeanObject = core::ptr::null_mut();
    v_res_1516_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_1513_, v_a_1514_);
    lean_dec(v_a_1514_);
    return v_res_1516_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivNat(
    mut v_e_1517_: *mut LeanObject,
    mut v_a_1518_: *mut LeanObject,
    mut v_a_1519_: *mut LeanObject,
    mut v_a_1520_: *mut LeanObject,
    mut v_a_1521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    v___x_1523_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_1517_, v_a_1519_);
    return v___x_1523_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHDivNat___boxed(
    mut v_e_1524_: *mut LeanObject,
    mut v_a_1525_: *mut LeanObject,
    mut v_a_1526_: *mut LeanObject,
    mut v_a_1527_: *mut LeanObject,
    mut v_a_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1530_: *mut LeanObject = core::ptr::null_mut();
    v_res_1530_ =
        l_Lean_Meta_Structural_isInstHDivNat(v_e_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
    lean_dec(v_a_1528_);
    lean_dec_ref(v_a_1527_);
    lean_dec(v_a_1526_);
    lean_dec_ref(v_a_1525_);
    return v_res_1530_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModNat___redArg(
    mut v_e_1534_: *mut LeanObject,
    mut v_a_1535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1541_: u8 = 0;
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v_arg_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: u8 = 0;
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v_a_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1561_: u8 = 0;
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1537_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1534_, v_a_1535_);
                if lean_obj_tag(v___x_1537_) == 0 {
                    v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
                    v_isSharedCheck_1557_ = (!lean_is_exclusive(v___x_1537_)) as u8;
                    if v_isSharedCheck_1557_ == 0 {
                        v___x_1540_ = v___x_1537_;
                        v_isShared_1541_ = v_isSharedCheck_1557_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1538_);
                        lean_dec(v___x_1537_);
                        v___x_1540_ = lean_box(0);
                        v_isShared_1541_ = v_isSharedCheck_1557_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1558_ = lean_ctor_get(v___x_1537_, 0);
                    v_isSharedCheck_1565_ = (!lean_is_exclusive(v___x_1537_)) as u8;
                    if v_isSharedCheck_1565_ == 0 {
                        v___x_1560_ = v___x_1537_;
                        v_isShared_1561_ = v_isSharedCheck_1565_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1558_);
                        lean_dec(v___x_1537_);
                        v___x_1560_ = lean_box(0);
                        v_isShared_1561_ = v_isSharedCheck_1565_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1548_ = l_Lean_Expr_cleanupAnnotations(v_a_1538_);
                v___x_1549_ = l_Lean_Expr_isApp(v___x_1548_);
                if v___x_1549_ == 0 {
                    lean_dec_ref(v___x_1548_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1550_ = lean_ctor_get(v___x_1548_, 1);
                    lean_inc_ref(v_arg_1550_);
                    v___x_1551_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1548_);
                    v___x_1552_ = l_Lean_Expr_isApp(v___x_1551_);
                    if v___x_1552_ == 0 {
                        lean_dec_ref(v___x_1551_);
                        lean_dec_ref(v_arg_1550_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1553_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1551_);
                        v___x_1554_ = l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1;
                        v___x_1555_ = l_Lean_Expr_isConstOf(v___x_1553_, v___x_1554_);
                        lean_dec_ref(v___x_1553_);
                        if v___x_1555_ == 0 {
                            lean_dec_ref(v_arg_1550_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_1540_);
                            v___x_1556_ = l_Lean_Meta_Structural_isInstModNat___redArg(
                                v_arg_1550_,
                                v_a_1535_,
                            );
                            return v___x_1556_;
                        }
                    }
                }
            }
            2 => {
                v___x_1543_ = 0;
                v___x_1544_ = lean_box((v___x_1543_) as usize);
                if v_isShared_1541_ == 0 {
                    lean_ctor_set(v___x_1540_, 0, v___x_1544_);
                    v___x_1546_ = v___x_1540_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
                    v___x_1546_ = v_reuseFailAlloc_1547_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1546_;
            }
            4 => {
                if v_isShared_1561_ == 0 {
                    v___x_1563_ = v___x_1560_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
                    v___x_1563_ = v_reuseFailAlloc_1564_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModNat___redArg___boxed(
    mut v_e_1566_: *mut LeanObject,
    mut v_a_1567_: *mut LeanObject,
    mut v_a_1568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1569_: *mut LeanObject = core::ptr::null_mut();
    v_res_1569_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_1566_, v_a_1567_);
    lean_dec(v_a_1567_);
    return v_res_1569_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModNat(
    mut v_e_1570_: *mut LeanObject,
    mut v_a_1571_: *mut LeanObject,
    mut v_a_1572_: *mut LeanObject,
    mut v_a_1573_: *mut LeanObject,
    mut v_a_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_1570_, v_a_1572_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHModNat___boxed(
    mut v_e_1577_: *mut LeanObject,
    mut v_a_1578_: *mut LeanObject,
    mut v_a_1579_: *mut LeanObject,
    mut v_a_1580_: *mut LeanObject,
    mut v_a_1581_: *mut LeanObject,
    mut v_a_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1583_: *mut LeanObject = core::ptr::null_mut();
    v_res_1583_ =
        l_Lean_Meta_Structural_isInstHModNat(v_e_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
    lean_dec(v_a_1581_);
    lean_dec_ref(v_a_1580_);
    lean_dec(v_a_1579_);
    lean_dec_ref(v_a_1578_);
    return v_res_1583_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowNat___redArg(
    mut v_e_1587_: *mut LeanObject,
    mut v_a_1588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u8 = 0;
    let mut v_arg_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v_a_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1616_: u8 = 0;
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1590_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1587_, v_a_1588_);
                if lean_obj_tag(v___x_1590_) == 0 {
                    v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
                    v_isSharedCheck_1612_ = (!lean_is_exclusive(v___x_1590_)) as u8;
                    if v_isSharedCheck_1612_ == 0 {
                        v___x_1593_ = v___x_1590_;
                        v_isShared_1594_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1591_);
                        lean_dec(v___x_1590_);
                        v___x_1593_ = lean_box(0);
                        v_isShared_1594_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1613_ = lean_ctor_get(v___x_1590_, 0);
                    v_isSharedCheck_1620_ = (!lean_is_exclusive(v___x_1590_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1615_ = v___x_1590_;
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1613_);
                        lean_dec(v___x_1590_);
                        v___x_1615_ = lean_box(0);
                        v_isShared_1616_ = v_isSharedCheck_1620_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1601_ = l_Lean_Expr_cleanupAnnotations(v_a_1591_);
                v___x_1602_ = l_Lean_Expr_isApp(v___x_1601_);
                if v___x_1602_ == 0 {
                    lean_dec_ref(v___x_1601_);
                    state = 2;
                    continue;
                } else {
                    v_arg_1603_ = lean_ctor_get(v___x_1601_, 1);
                    lean_inc_ref(v_arg_1603_);
                    v___x_1604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1601_);
                    v___x_1605_ = l_Lean_Expr_isApp(v___x_1604_);
                    if v___x_1605_ == 0 {
                        lean_dec_ref(v___x_1604_);
                        lean_dec_ref(v_arg_1603_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1604_);
                        v___x_1607_ = l_Lean_Expr_isApp(v___x_1606_);
                        if v___x_1607_ == 0 {
                            lean_dec_ref(v___x_1606_);
                            lean_dec_ref(v_arg_1603_);
                            state = 2;
                            continue;
                        } else {
                            v___x_1608_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1606_);
                            v___x_1609_ = l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1;
                            v___x_1610_ = l_Lean_Expr_isConstOf(v___x_1608_, v___x_1609_);
                            lean_dec_ref(v___x_1608_);
                            if v___x_1610_ == 0 {
                                lean_dec_ref(v_arg_1603_);
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_1593_);
                                v___x_1611_ = l_Lean_Meta_Structural_isInstPowNat___redArg(
                                    v_arg_1603_,
                                    v_a_1588_,
                                );
                                return v___x_1611_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_1596_ = 0;
                v___x_1597_ = lean_box((v___x_1596_) as usize);
                if v_isShared_1594_ == 0 {
                    lean_ctor_set(v___x_1593_, 0, v___x_1597_);
                    v___x_1599_ = v___x_1593_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
                    v___x_1599_ = v_reuseFailAlloc_1600_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1599_;
            }
            4 => {
                if v_isShared_1616_ == 0 {
                    v___x_1618_ = v___x_1615_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
                    v___x_1618_ = v_reuseFailAlloc_1619_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowNat___redArg___boxed(
    mut v_e_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_a_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1624_: *mut LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_1621_, v_a_1622_);
    lean_dec(v_a_1622_);
    return v_res_1624_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowNat(
    mut v_e_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
    mut v_a_1627_: *mut LeanObject,
    mut v_a_1628_: *mut LeanObject,
    mut v_a_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1631_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_1625_, v_a_1627_);
    return v___x_1631_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstHPowNat___boxed(
    mut v_e_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1638_: *mut LeanObject = core::ptr::null_mut();
    v_res_1638_ =
        l_Lean_Meta_Structural_isInstHPowNat(v_e_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
    lean_dec(v_a_1636_);
    lean_dec_ref(v_a_1635_);
    lean_dec(v_a_1634_);
    lean_dec_ref(v_a_1633_);
    return v_res_1638_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTNat___redArg(
    mut v_e_1642_: *mut LeanObject,
    mut v_a_1643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1657_: u8 = 0;
    let mut v_a_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1661_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1645_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1642_, v_a_1643_);
                if lean_obj_tag(v___x_1645_) == 0 {
                    v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
                    v_isSharedCheck_1657_ = (!lean_is_exclusive(v___x_1645_)) as u8;
                    if v_isSharedCheck_1657_ == 0 {
                        v___x_1648_ = v___x_1645_;
                        v_isShared_1649_ = v_isSharedCheck_1657_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1646_);
                        lean_dec(v___x_1645_);
                        v___x_1648_ = lean_box(0);
                        v_isShared_1649_ = v_isSharedCheck_1657_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1658_ = lean_ctor_get(v___x_1645_, 0);
                    v_isSharedCheck_1665_ = (!lean_is_exclusive(v___x_1645_)) as u8;
                    if v_isSharedCheck_1665_ == 0 {
                        v___x_1660_ = v___x_1645_;
                        v_isShared_1661_ = v_isSharedCheck_1665_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1658_);
                        lean_dec(v___x_1645_);
                        v___x_1660_ = lean_box(0);
                        v_isShared_1661_ = v_isSharedCheck_1665_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1650_ = l_Lean_Expr_cleanupAnnotations(v_a_1646_);
                v___x_1651_ = l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1;
                v___x_1652_ = l_Lean_Expr_isConstOf(v___x_1650_, v___x_1651_);
                lean_dec_ref(v___x_1650_);
                v___x_1653_ = lean_box((v___x_1652_) as usize);
                if v_isShared_1649_ == 0 {
                    lean_ctor_set(v___x_1648_, 0, v___x_1653_);
                    v___x_1655_ = v___x_1648_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1653_);
                    v___x_1655_ = v_reuseFailAlloc_1656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1655_;
            }
            3 => {
                if v_isShared_1661_ == 0 {
                    v___x_1663_ = v___x_1660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
                    v___x_1663_ = v_reuseFailAlloc_1664_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTNat___redArg___boxed(
    mut v_e_1666_: *mut LeanObject,
    mut v_a_1667_: *mut LeanObject,
    mut v_a_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1669_: *mut LeanObject = core::ptr::null_mut();
    v_res_1669_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_1666_, v_a_1667_);
    lean_dec(v_a_1667_);
    return v_res_1669_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTNat(
    mut v_e_1670_: *mut LeanObject,
    mut v_a_1671_: *mut LeanObject,
    mut v_a_1672_: *mut LeanObject,
    mut v_a_1673_: *mut LeanObject,
    mut v_a_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    v___x_1676_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_1670_, v_a_1672_);
    return v___x_1676_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLTNat___boxed(
    mut v_e_1677_: *mut LeanObject,
    mut v_a_1678_: *mut LeanObject,
    mut v_a_1679_: *mut LeanObject,
    mut v_a_1680_: *mut LeanObject,
    mut v_a_1681_: *mut LeanObject,
    mut v_a_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1683_: *mut LeanObject = core::ptr::null_mut();
    v_res_1683_ =
        l_Lean_Meta_Structural_isInstLTNat(v_e_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_);
    lean_dec(v_a_1681_);
    lean_dec_ref(v_a_1680_);
    lean_dec(v_a_1679_);
    lean_dec_ref(v_a_1678_);
    return v_res_1683_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLENat___redArg(
    mut v_e_1687_: *mut LeanObject,
    mut v_a_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1694_: u8 = 0;
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1702_: u8 = 0;
    let mut v_a_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1706_: u8 = 0;
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1710_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1690_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1687_, v_a_1688_);
                if lean_obj_tag(v___x_1690_) == 0 {
                    v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
                    v_isSharedCheck_1702_ = (!lean_is_exclusive(v___x_1690_)) as u8;
                    if v_isSharedCheck_1702_ == 0 {
                        v___x_1693_ = v___x_1690_;
                        v_isShared_1694_ = v_isSharedCheck_1702_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1691_);
                        lean_dec(v___x_1690_);
                        v___x_1693_ = lean_box(0);
                        v_isShared_1694_ = v_isSharedCheck_1702_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1703_ = lean_ctor_get(v___x_1690_, 0);
                    v_isSharedCheck_1710_ = (!lean_is_exclusive(v___x_1690_)) as u8;
                    if v_isSharedCheck_1710_ == 0 {
                        v___x_1705_ = v___x_1690_;
                        v_isShared_1706_ = v_isSharedCheck_1710_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1703_);
                        lean_dec(v___x_1690_);
                        v___x_1705_ = lean_box(0);
                        v_isShared_1706_ = v_isSharedCheck_1710_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1695_ = l_Lean_Expr_cleanupAnnotations(v_a_1691_);
                v___x_1696_ = l_Lean_Meta_Structural_isInstLENat___redArg___closed__1;
                v___x_1697_ = l_Lean_Expr_isConstOf(v___x_1695_, v___x_1696_);
                lean_dec_ref(v___x_1695_);
                v___x_1698_ = lean_box((v___x_1697_) as usize);
                if v_isShared_1694_ == 0 {
                    lean_ctor_set(v___x_1693_, 0, v___x_1698_);
                    v___x_1700_ = v___x_1693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
                    v___x_1700_ = v_reuseFailAlloc_1701_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1700_;
            }
            3 => {
                if v_isShared_1706_ == 0 {
                    v___x_1708_ = v___x_1705_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
                    v___x_1708_ = v_reuseFailAlloc_1709_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstLENat___redArg___boxed(
    mut v_e_1711_: *mut LeanObject,
    mut v_a_1712_: *mut LeanObject,
    mut v_a_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1714_: *mut LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_1711_, v_a_1712_);
    lean_dec(v_a_1712_);
    return v_res_1714_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLENat(
    mut v_e_1715_: *mut LeanObject,
    mut v_a_1716_: *mut LeanObject,
    mut v_a_1717_: *mut LeanObject,
    mut v_a_1718_: *mut LeanObject,
    mut v_a_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_1715_, v_a_1717_);
    return v___x_1721_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstLENat___boxed(
    mut v_e_1722_: *mut LeanObject,
    mut v_a_1723_: *mut LeanObject,
    mut v_a_1724_: *mut LeanObject,
    mut v_a_1725_: *mut LeanObject,
    mut v_a_1726_: *mut LeanObject,
    mut v_a_1727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1728_: *mut LeanObject = core::ptr::null_mut();
    v_res_1728_ =
        l_Lean_Meta_Structural_isInstLENat(v_e_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_);
    lean_dec(v_a_1726_);
    lean_dec_ref(v_a_1725_);
    lean_dec(v_a_1724_);
    lean_dec_ref(v_a_1723_);
    return v_res_1728_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdNat___redArg(
    mut v_e_1733_: *mut LeanObject,
    mut v_a_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: u8 = 0;
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1748_: u8 = 0;
    let mut v_a_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1756_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1736_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1733_, v_a_1734_);
                if lean_obj_tag(v___x_1736_) == 0 {
                    v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
                    v_isSharedCheck_1748_ = (!lean_is_exclusive(v___x_1736_)) as u8;
                    if v_isSharedCheck_1748_ == 0 {
                        v___x_1739_ = v___x_1736_;
                        v_isShared_1740_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1737_);
                        lean_dec(v___x_1736_);
                        v___x_1739_ = lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1748_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1749_ = lean_ctor_get(v___x_1736_, 0);
                    v_isSharedCheck_1756_ = (!lean_is_exclusive(v___x_1736_)) as u8;
                    if v_isSharedCheck_1756_ == 0 {
                        v___x_1751_ = v___x_1736_;
                        v_isShared_1752_ = v_isSharedCheck_1756_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1749_);
                        lean_dec(v___x_1736_);
                        v___x_1751_ = lean_box(0);
                        v_isShared_1752_ = v_isSharedCheck_1756_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1741_ = l_Lean_Expr_cleanupAnnotations(v_a_1737_);
                v___x_1742_ = l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1;
                v___x_1743_ = l_Lean_Expr_isConstOf(v___x_1741_, v___x_1742_);
                lean_dec_ref(v___x_1741_);
                v___x_1744_ = lean_box((v___x_1743_) as usize);
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 0, v___x_1744_);
                    v___x_1746_ = v___x_1739_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1744_);
                    v___x_1746_ = v_reuseFailAlloc_1747_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1746_;
            }
            3 => {
                if v_isShared_1752_ == 0 {
                    v___x_1754_ = v___x_1751_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
                    v___x_1754_ = v_reuseFailAlloc_1755_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1754_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdNat___redArg___boxed(
    mut v_e_1757_: *mut LeanObject,
    mut v_a_1758_: *mut LeanObject,
    mut v_a_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1760_: *mut LeanObject = core::ptr::null_mut();
    v_res_1760_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_1757_, v_a_1758_);
    lean_dec(v_a_1758_);
    return v_res_1760_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdNat(
    mut v_e_1761_: *mut LeanObject,
    mut v_a_1762_: *mut LeanObject,
    mut v_a_1763_: *mut LeanObject,
    mut v_a_1764_: *mut LeanObject,
    mut v_a_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v___x_1767_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_1761_, v_a_1763_);
    return v___x_1767_;
}
pub unsafe fn l_Lean_Meta_Structural_isInstDvdNat___boxed(
    mut v_e_1768_: *mut LeanObject,
    mut v_a_1769_: *mut LeanObject,
    mut v_a_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
    mut v_a_1772_: *mut LeanObject,
    mut v_a_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1774_: *mut LeanObject = core::ptr::null_mut();
    v_res_1774_ =
        l_Lean_Meta_Structural_isInstDvdNat(v_e_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
    lean_dec(v_a_1772_);
    lean_dec_ref(v_a_1771_);
    lean_dec(v_a_1770_);
    lean_dec_ref(v_a_1769_);
    return v_res_1774_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstAddNat(
    mut v_e_1775_: *mut LeanObject,
    mut v_a_1776_: *mut LeanObject,
    mut v_a_1777_: *mut LeanObject,
    mut v_a_1778_: *mut LeanObject,
    mut v_a_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_1775_);
    v___x_1781_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_1775_, v_a_1777_);
    if lean_obj_tag(v___x_1781_) == 0 {
        let mut v_a_1782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: u8 = 0;
        v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
        lean_inc(v_a_1782_);
        v___x_1783_ = (lean_unbox(v_a_1782_) as u8);
        lean_dec(v_a_1782_);
        if v___x_1783_ == 0 {
            let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1781_, 1);
            v___x_1784_ = l_Lean_Nat_mkInstAdd;
            v___x_1785_ = l_Lean_Meta_isDefEqI(
                v_e_1775_,
                v___x_1784_,
                v_a_1776_,
                v_a_1777_,
                v_a_1778_,
                v_a_1779_,
            );
            return v___x_1785_;
        } else {
            lean_dec_ref(v_e_1775_);
            return v___x_1781_;
        }
    } else {
        lean_dec_ref(v_e_1775_);
        return v___x_1781_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstAddNat___boxed(
    mut v_e_1786_: *mut LeanObject,
    mut v_a_1787_: *mut LeanObject,
    mut v_a_1788_: *mut LeanObject,
    mut v_a_1789_: *mut LeanObject,
    mut v_a_1790_: *mut LeanObject,
    mut v_a_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1792_: *mut LeanObject = core::ptr::null_mut();
    v_res_1792_ =
        l_Lean_Meta_DefEq_isInstAddNat(v_e_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_);
    lean_dec(v_a_1790_);
    lean_dec_ref(v_a_1789_);
    lean_dec(v_a_1788_);
    lean_dec_ref(v_a_1787_);
    return v_res_1792_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHAddNat(
    mut v_e_1793_: *mut LeanObject,
    mut v_a_1794_: *mut LeanObject,
    mut v_a_1795_: *mut LeanObject,
    mut v_a_1796_: *mut LeanObject,
    mut v_a_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_1793_);
    v___x_1799_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_1793_, v_a_1795_);
    if lean_obj_tag(v___x_1799_) == 0 {
        let mut v_a_1800_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1801_: u8 = 0;
        v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
        lean_inc(v_a_1800_);
        v___x_1801_ = (lean_unbox(v_a_1800_) as u8);
        lean_dec(v_a_1800_);
        if v___x_1801_ == 0 {
            let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1799_, 1);
            v___x_1802_ = l_Lean_Nat_mkInstHAdd;
            v___x_1803_ = l_Lean_Meta_isDefEqI(
                v_e_1793_,
                v___x_1802_,
                v_a_1794_,
                v_a_1795_,
                v_a_1796_,
                v_a_1797_,
            );
            return v___x_1803_;
        } else {
            lean_dec_ref(v_e_1793_);
            return v___x_1799_;
        }
    } else {
        lean_dec_ref(v_e_1793_);
        return v___x_1799_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHAddNat___boxed(
    mut v_e_1804_: *mut LeanObject,
    mut v_a_1805_: *mut LeanObject,
    mut v_a_1806_: *mut LeanObject,
    mut v_a_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
    mut v_a_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1810_: *mut LeanObject = core::ptr::null_mut();
    v_res_1810_ =
        l_Lean_Meta_DefEq_isInstHAddNat(v_e_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_);
    lean_dec(v_a_1808_);
    lean_dec_ref(v_a_1807_);
    lean_dec(v_a_1806_);
    lean_dec_ref(v_a_1805_);
    return v_res_1810_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstMulNat(
    mut v_e_1811_: *mut LeanObject,
    mut v_a_1812_: *mut LeanObject,
    mut v_a_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_1811_);
    v___x_1817_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_1811_, v_a_1813_);
    if lean_obj_tag(v___x_1817_) == 0 {
        let mut v_a_1818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1819_: u8 = 0;
        v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
        lean_inc(v_a_1818_);
        v___x_1819_ = (lean_unbox(v_a_1818_) as u8);
        lean_dec(v_a_1818_);
        if v___x_1819_ == 0 {
            let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1817_, 1);
            v___x_1820_ = l_Lean_Nat_mkInstMul;
            v___x_1821_ = l_Lean_Meta_isDefEqI(
                v_e_1811_,
                v___x_1820_,
                v_a_1812_,
                v_a_1813_,
                v_a_1814_,
                v_a_1815_,
            );
            return v___x_1821_;
        } else {
            lean_dec_ref(v_e_1811_);
            return v___x_1817_;
        }
    } else {
        lean_dec_ref(v_e_1811_);
        return v___x_1817_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstMulNat___boxed(
    mut v_e_1822_: *mut LeanObject,
    mut v_a_1823_: *mut LeanObject,
    mut v_a_1824_: *mut LeanObject,
    mut v_a_1825_: *mut LeanObject,
    mut v_a_1826_: *mut LeanObject,
    mut v_a_1827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1828_: *mut LeanObject = core::ptr::null_mut();
    v_res_1828_ =
        l_Lean_Meta_DefEq_isInstMulNat(v_e_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
    lean_dec(v_a_1826_);
    lean_dec_ref(v_a_1825_);
    lean_dec(v_a_1824_);
    lean_dec_ref(v_a_1823_);
    return v_res_1828_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHMulNat(
    mut v_e_1829_: *mut LeanObject,
    mut v_a_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_1829_);
    v___x_1835_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_1829_, v_a_1831_);
    if lean_obj_tag(v___x_1835_) == 0 {
        let mut v_a_1836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1837_: u8 = 0;
        v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
        lean_inc(v_a_1836_);
        v___x_1837_ = (lean_unbox(v_a_1836_) as u8);
        lean_dec(v_a_1836_);
        if v___x_1837_ == 0 {
            let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1835_, 1);
            v___x_1838_ = l_Lean_Nat_mkInstHMul;
            v___x_1839_ = l_Lean_Meta_isDefEqI(
                v_e_1829_,
                v___x_1838_,
                v_a_1830_,
                v_a_1831_,
                v_a_1832_,
                v_a_1833_,
            );
            return v___x_1839_;
        } else {
            lean_dec_ref(v_e_1829_);
            return v___x_1835_;
        }
    } else {
        lean_dec_ref(v_e_1829_);
        return v___x_1835_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstHMulNat___boxed(
    mut v_e_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
    mut v_a_1842_: *mut LeanObject,
    mut v_a_1843_: *mut LeanObject,
    mut v_a_1844_: *mut LeanObject,
    mut v_a_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1846_: *mut LeanObject = core::ptr::null_mut();
    v_res_1846_ =
        l_Lean_Meta_DefEq_isInstHMulNat(v_e_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
    lean_dec(v_a_1844_);
    lean_dec_ref(v_a_1843_);
    lean_dec(v_a_1842_);
    lean_dec_ref(v_a_1841_);
    return v_res_1846_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLTNat(
    mut v_e_1847_: *mut LeanObject,
    mut v_a_1848_: *mut LeanObject,
    mut v_a_1849_: *mut LeanObject,
    mut v_a_1850_: *mut LeanObject,
    mut v_a_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_1847_);
    v___x_1853_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_1847_, v_a_1849_);
    if lean_obj_tag(v___x_1853_) == 0 {
        let mut v_a_1854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: u8 = 0;
        v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
        lean_inc(v_a_1854_);
        v___x_1855_ = (lean_unbox(v_a_1854_) as u8);
        lean_dec(v_a_1854_);
        if v___x_1855_ == 0 {
            let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1853_, 1);
            v___x_1856_ = l_Lean_Nat_mkInstLT;
            v___x_1857_ = l_Lean_Meta_isDefEqI(
                v_e_1847_,
                v___x_1856_,
                v_a_1848_,
                v_a_1849_,
                v_a_1850_,
                v_a_1851_,
            );
            return v___x_1857_;
        } else {
            lean_dec_ref(v_e_1847_);
            return v___x_1853_;
        }
    } else {
        lean_dec_ref(v_e_1847_);
        return v___x_1853_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLTNat___boxed(
    mut v_e_1858_: *mut LeanObject,
    mut v_a_1859_: *mut LeanObject,
    mut v_a_1860_: *mut LeanObject,
    mut v_a_1861_: *mut LeanObject,
    mut v_a_1862_: *mut LeanObject,
    mut v_a_1863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1864_: *mut LeanObject = core::ptr::null_mut();
    v_res_1864_ =
        l_Lean_Meta_DefEq_isInstLTNat(v_e_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
    lean_dec(v_a_1862_);
    lean_dec_ref(v_a_1861_);
    lean_dec(v_a_1860_);
    lean_dec_ref(v_a_1859_);
    return v_res_1864_;
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLENat(
    mut v_e_1865_: *mut LeanObject,
    mut v_a_1866_: *mut LeanObject,
    mut v_a_1867_: *mut LeanObject,
    mut v_a_1868_: *mut LeanObject,
    mut v_a_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_1865_);
    v___x_1871_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_1865_, v_a_1867_);
    if lean_obj_tag(v___x_1871_) == 0 {
        let mut v_a_1872_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1873_: u8 = 0;
        v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
        lean_inc(v_a_1872_);
        v___x_1873_ = (lean_unbox(v_a_1872_) as u8);
        lean_dec(v_a_1872_);
        if v___x_1873_ == 0 {
            let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_1871_, 1);
            v___x_1874_ = l_Lean_Nat_mkInstLE;
            v___x_1875_ = l_Lean_Meta_isDefEqI(
                v_e_1865_,
                v___x_1874_,
                v_a_1866_,
                v_a_1867_,
                v_a_1868_,
                v_a_1869_,
            );
            return v___x_1875_;
        } else {
            lean_dec_ref(v_e_1865_);
            return v___x_1871_;
        }
    } else {
        lean_dec_ref(v_e_1865_);
        return v___x_1871_;
    }
}
pub unsafe fn l_Lean_Meta_DefEq_isInstLENat___boxed(
    mut v_e_1876_: *mut LeanObject,
    mut v_a_1877_: *mut LeanObject,
    mut v_a_1878_: *mut LeanObject,
    mut v_a_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1882_: *mut LeanObject = core::ptr::null_mut();
    v_res_1882_ =
        l_Lean_Meta_DefEq_isInstLENat(v_e_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
    lean_dec(v_a_1880_);
    lean_dec_ref(v_a_1879_);
    lean_dec(v_a_1878_);
    lean_dec_ref(v_a_1877_);
    return v_res_1882_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_NatInstTesters(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_NatInstTesters(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_NatInstTesters(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_NatInstTesters(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_NatInstTesters(builtin);
}
