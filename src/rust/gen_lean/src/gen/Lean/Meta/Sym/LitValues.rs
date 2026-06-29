// Lean compiler output
// Module: Lean.Meta.Sym.LitValues
// Imports: Lean.Expr Init.Data.Rat
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_div, l_Rat_ofInt};
use crate::r#gen::Init::Data::Rat::{initialize_Init_Data_Rat, runtime_initialize_Init_Data_Rat};
use crate::r#gen::Init::Prelude::{l_BitVec_ofNat, l_Char_ofNat};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{lean_int_neg, lean_nat_to_int};
use crate::lean_imports_rs::Init::Data::SInt::Basic::{
    lean_int8_of_int, lean_int16_of_int, lean_int32_of_int, lean_int64_of_int,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint16_of_nat, lean_uint32_of_nat, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_mod, lean_uint8_of_nat};
pub static l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [79, 102, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Sym_getNatValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [111, 102, 78, 97, 116, 0],
    };
static mut l_Lean_Meta_Sym_getNatValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17636616155771105671 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15578568367168711682 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getNatValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_getIntValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_getIntValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9626815015619986526 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            17185717442815859305 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getIntValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [72, 68, 105, 118, 0],
    };
static mut l_Lean_Meta_Sym_getRatValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [104, 68, 105, 118, 0],
    };
static mut l_Lean_Meta_Sym_getRatValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11858238400308895562 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            6100819061652633370 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getRatValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [66, 105, 116, 86, 101, 99, 0],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7578295756008745317 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [111, 102, 78, 97, 116, 76, 84, 0],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2059920148364733515 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [70, 105, 110, 0],
    };
static mut l_Lean_Meta_Sym_getFinValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15815496672699636542 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getFinValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [67, 104, 97, 114, 0],
    };
static mut l_Lean_Meta_Sym_getCharValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14164462494711235346 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18098914779984442139 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getCharValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_getNatValue_x3f(
    mut v_e_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: u8 = 0;
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: u8 = 0;
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: u8 = 0;
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: u8 = 0;
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_397_ = l_Lean_Expr_cleanupAnnotations(v_e_396_);
                v___x_398_ = l_Lean_Expr_isApp(v___x_397_);
                if v___x_398_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_397_);
                    v___x_399_ = crate::leanh::lean_box(0);
                    return v___x_399_;
                } else {
                    v___x_400_ = l_Lean_Expr_appFnCleanup___redArg(v___x_397_);
                    v___x_401_ = l_Lean_Expr_isApp(v___x_400_);
                    if v___x_401_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_400_);
                        v___x_402_ = crate::leanh::lean_box(0);
                        return v___x_402_;
                    } else {
                        v_arg_403_ = crate::leanh::lean_ctor_get(v___x_400_, 1);
                        crate::leanh::lean_inc_ref(v_arg_403_);
                        v___x_404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
                        v___x_405_ = l_Lean_Expr_isApp(v___x_404_);
                        if v___x_405_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_404_);
                            crate::leanh::lean_dec_ref(v_arg_403_);
                            v___x_406_ = crate::leanh::lean_box(0);
                            return v___x_406_;
                        } else {
                            v___x_407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_404_);
                            v___x_408_ = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
                            v___x_409_ = l_Lean_Expr_isConstOf(v___x_407_, v___x_408_);
                            crate::leanh::lean_dec_ref(v___x_407_);
                            if v___x_409_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_403_);
                                v___x_410_ = crate::leanh::lean_box(0);
                                return v___x_410_;
                            } else {
                                if crate::leanh::lean_obj_tag(v_arg_403_) == 9 {
                                    v_a_411_ = crate::leanh::lean_ctor_get(v_arg_403_, 0);
                                    crate::leanh::lean_inc_ref(v_a_411_);
                                    crate::leanh::lean_dec_ref_known(v_arg_403_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_411_) == 0 {
                                        v_val_412_ = crate::leanh::lean_ctor_get(v_a_411_, 0);
                                        v_isSharedCheck_419_ =
                                            (!crate::leanh::lean_is_exclusive(v_a_411_)) as u8;
                                        if v_isSharedCheck_419_ == 0 {
                                            v___x_414_ = v_a_411_;
                                            v_isShared_415_ = v_isSharedCheck_419_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_val_412_);
                                            crate::leanh::lean_dec(v_a_411_);
                                            v___x_414_ = crate::leanh::lean_box(0);
                                            v_isShared_415_ = v_isSharedCheck_419_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_a_411_);
                                        v___x_420_ = crate::leanh::lean_box(0);
                                        return v___x_420_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_403_);
                                    v___x_421_ = crate::leanh::lean_box(0);
                                    return v___x_421_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_415_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_414_, 1);
                    v___x_417_ = v___x_414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_418_, 0, v_val_412_);
                    v___x_417_ = v_reuseFailAlloc_418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(
    mut v_a_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = lean_nat_to_int(v_a_422_);
    return v___x_423_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntValue_x3f(
    mut v_e_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_436_: u8 = 0;
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_441_: u8 = 0;
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    let mut v_arg_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u8 = 0;
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: u8 = 0;
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_457_: u8 = 0;
    let mut v___x_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_429_);
                v___x_442_ = l_Lean_Expr_cleanupAnnotations(v_e_429_);
                v___x_443_ = l_Lean_Expr_isApp(v___x_442_);
                if v___x_443_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_442_);
                    state = 1;
                    continue;
                } else {
                    v_arg_444_ = crate::leanh::lean_ctor_get(v___x_442_, 1);
                    crate::leanh::lean_inc_ref(v_arg_444_);
                    v___x_445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_442_);
                    v___x_446_ = l_Lean_Expr_isApp(v___x_445_);
                    if v___x_446_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_445_);
                        crate::leanh::lean_dec_ref(v_arg_444_);
                        state = 1;
                        continue;
                    } else {
                        v___x_447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_445_);
                        v___x_448_ = l_Lean_Expr_isApp(v___x_447_);
                        if v___x_448_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_447_);
                            crate::leanh::lean_dec_ref(v_arg_444_);
                            state = 1;
                            continue;
                        } else {
                            v___x_449_ = l_Lean_Expr_appFnCleanup___redArg(v___x_447_);
                            v___x_450_ = l_Lean_Meta_Sym_getIntValue_x3f___closed__2;
                            v___x_451_ = l_Lean_Expr_isConstOf(v___x_449_, v___x_450_);
                            crate::leanh::lean_dec_ref(v___x_449_);
                            if v___x_451_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_444_);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_e_429_);
                                v___x_452_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_444_);
                                if crate::leanh::lean_obj_tag(v___x_452_) == 0 {
                                    v___x_453_ = crate::leanh::lean_box(0);
                                    return v___x_453_;
                                } else {
                                    v_val_454_ = crate::leanh::lean_ctor_get(v___x_452_, 0);
                                    v_isSharedCheck_463_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_452_)) as u8;
                                    if v_isSharedCheck_463_ == 0 {
                                        v___x_456_ = v___x_452_;
                                        v_isShared_457_ = v_isSharedCheck_463_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_454_);
                                        crate::leanh::lean_dec(v___x_452_);
                                        v___x_456_ = crate::leanh::lean_box(0);
                                        v_isShared_457_ = v_isSharedCheck_463_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_431_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_429_);
                if crate::leanh::lean_obj_tag(v___x_431_) == 0 {
                    v___x_432_ = crate::leanh::lean_box(0);
                    return v___x_432_;
                } else {
                    v_val_433_ = crate::leanh::lean_ctor_get(v___x_431_, 0);
                    v_isSharedCheck_441_ = (!crate::leanh::lean_is_exclusive(v___x_431_)) as u8;
                    if v_isSharedCheck_441_ == 0 {
                        v___x_435_ = v___x_431_;
                        v_isShared_436_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_433_);
                        crate::leanh::lean_dec(v___x_431_);
                        v___x_435_ = crate::leanh::lean_box(0);
                        v_isShared_436_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_437_ = lean_nat_to_int(v_val_433_);
                if v_isShared_436_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_435_, 0, v___x_437_);
                    v___x_439_ = v___x_435_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_440_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
                    v___x_439_ = v_reuseFailAlloc_440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_439_;
            }
            4 => {
                v___x_458_ = lean_nat_to_int(v_val_454_);
                v___x_459_ = lean_int_neg(v___x_458_);
                crate::leanh::lean_dec(v___x_458_);
                if v_isShared_457_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_456_, 0, v___x_459_);
                    v___x_461_ = v___x_456_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
                    v___x_461_ = v_reuseFailAlloc_462_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_461_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(
    mut v_a_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = l_Rat_ofInt(v_a_464_);
    return v___x_465_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(
    mut v_a_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = lean_nat_to_int(v_a_466_);
    v___x_468_ = l_Rat_ofInt(v___x_467_);
    return v___x_468_;
}
pub unsafe fn l_Lean_Meta_Sym_getRatValue_x3f(
    mut v_e_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_481_: u8 = 0;
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v_arg_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: u8 = 0;
    let mut v_arg_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: u8 = 0;
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: u8 = 0;
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u8 = 0;
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_512_: u8 = 0;
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_474_);
                v___x_487_ = l_Lean_Expr_cleanupAnnotations(v_e_474_);
                v___x_488_ = l_Lean_Expr_isApp(v___x_487_);
                if v___x_488_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_487_);
                    state = 1;
                    continue;
                } else {
                    v_arg_489_ = crate::leanh::lean_ctor_get(v___x_487_, 1);
                    crate::leanh::lean_inc_ref(v_arg_489_);
                    v___x_490_ = l_Lean_Expr_appFnCleanup___redArg(v___x_487_);
                    v___x_491_ = l_Lean_Expr_isApp(v___x_490_);
                    if v___x_491_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_490_);
                        crate::leanh::lean_dec_ref(v_arg_489_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_492_ = crate::leanh::lean_ctor_get(v___x_490_, 1);
                        crate::leanh::lean_inc_ref(v_arg_492_);
                        v___x_493_ = l_Lean_Expr_appFnCleanup___redArg(v___x_490_);
                        v___x_494_ = l_Lean_Expr_isApp(v___x_493_);
                        if v___x_494_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_493_);
                            crate::leanh::lean_dec_ref(v_arg_492_);
                            crate::leanh::lean_dec_ref(v_arg_489_);
                            state = 1;
                            continue;
                        } else {
                            v___x_495_ = l_Lean_Expr_appFnCleanup___redArg(v___x_493_);
                            v___x_496_ = l_Lean_Expr_isApp(v___x_495_);
                            if v___x_496_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_495_);
                                crate::leanh::lean_dec_ref(v_arg_492_);
                                crate::leanh::lean_dec_ref(v_arg_489_);
                                state = 1;
                                continue;
                            } else {
                                v___x_497_ = l_Lean_Expr_appFnCleanup___redArg(v___x_495_);
                                v___x_498_ = l_Lean_Expr_isApp(v___x_497_);
                                if v___x_498_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_497_);
                                    crate::leanh::lean_dec_ref(v_arg_492_);
                                    crate::leanh::lean_dec_ref(v_arg_489_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_497_);
                                    v___x_500_ = l_Lean_Expr_isApp(v___x_499_);
                                    if v___x_500_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_499_);
                                        crate::leanh::lean_dec_ref(v_arg_492_);
                                        crate::leanh::lean_dec_ref(v_arg_489_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_499_);
                                        v___x_502_ = l_Lean_Meta_Sym_getRatValue_x3f___closed__2;
                                        v___x_503_ = l_Lean_Expr_isConstOf(v___x_501_, v___x_502_);
                                        crate::leanh::lean_dec_ref(v___x_501_);
                                        if v___x_503_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_492_);
                                            crate::leanh::lean_dec_ref(v_arg_489_);
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_e_474_);
                                            v___x_504_ =
                                                l_Lean_Meta_Sym_getIntValue_x3f(v_arg_492_);
                                            if crate::leanh::lean_obj_tag(v___x_504_) == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_489_);
                                                v___x_505_ = crate::leanh::lean_box(0);
                                                return v___x_505_;
                                            } else {
                                                v_val_506_ =
                                                    crate::leanh::lean_ctor_get(v___x_504_, 0);
                                                crate::leanh::lean_inc(v_val_506_);
                                                crate::leanh::lean_dec_ref_known(v___x_504_, 1);
                                                v___x_507_ =
                                                    l_Lean_Meta_Sym_getNatValue_x3f(v_arg_489_);
                                                if crate::leanh::lean_obj_tag(v___x_507_) == 0 {
                                                    crate::leanh::lean_dec(v_val_506_);
                                                    v___x_508_ = crate::leanh::lean_box(0);
                                                    return v___x_508_;
                                                } else {
                                                    v_val_509_ =
                                                        crate::leanh::lean_ctor_get(v___x_507_, 0);
                                                    v_isSharedCheck_519_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_507_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_519_ == 0 {
                                                        v___x_511_ = v___x_507_;
                                                        v_isShared_512_ = v_isSharedCheck_519_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_val_509_);
                                                        crate::leanh::lean_dec(v___x_507_);
                                                        v___x_511_ = crate::leanh::lean_box(0);
                                                        v_isShared_512_ = v_isSharedCheck_519_;
                                                        state = 4;
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
                }
            }
            1 => {
                v___x_476_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_474_);
                if crate::leanh::lean_obj_tag(v___x_476_) == 0 {
                    v___x_477_ = crate::leanh::lean_box(0);
                    return v___x_477_;
                } else {
                    v_val_478_ = crate::leanh::lean_ctor_get(v___x_476_, 0);
                    v_isSharedCheck_486_ = (!crate::leanh::lean_is_exclusive(v___x_476_)) as u8;
                    if v_isSharedCheck_486_ == 0 {
                        v___x_480_ = v___x_476_;
                        v_isShared_481_ = v_isSharedCheck_486_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_478_);
                        crate::leanh::lean_dec(v___x_476_);
                        v___x_480_ = crate::leanh::lean_box(0);
                        v_isShared_481_ = v_isSharedCheck_486_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_482_ = l_Rat_ofInt(v_val_478_);
                if v_isShared_481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_480_, 0, v___x_482_);
                    v___x_484_ = v___x_480_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
                    v___x_484_ = v_reuseFailAlloc_485_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_484_;
            }
            4 => {
                v___x_513_ = l_Rat_ofInt(v_val_506_);
                v___x_514_ = l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(v_val_509_);
                v___x_515_ = l_Rat_div(v___x_513_, v___x_514_);
                crate::leanh::lean_dec_ref(v___x_513_);
                if v_isShared_512_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_511_, 0, v___x_515_);
                    v___x_517_ = v___x_511_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
                    v___x_517_ = v_reuseFailAlloc_518_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_517_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getBitVecValue_x3f(
    mut v_e_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nExpr_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vExpr_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_542_: u8 = 0;
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_548_: u8 = 0;
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: u8 = 0;
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: u8 = 0;
    let mut v___x_560_: u8 = 0;
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: u8 = 0;
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_583_: u8 = 0;
    let mut v_val_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_549_ = l_Lean_Expr_cleanupAnnotations(v_e_530_);
                v___x_550_ = l_Lean_Expr_isApp(v___x_549_);
                if v___x_550_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_549_);
                    v___x_551_ = crate::leanh::lean_box(0);
                    return v___x_551_;
                } else {
                    v_arg_552_ = crate::leanh::lean_ctor_get(v___x_549_, 1);
                    crate::leanh::lean_inc_ref(v_arg_552_);
                    v___x_553_ = l_Lean_Expr_appFnCleanup___redArg(v___x_549_);
                    v___x_554_ = l_Lean_Expr_isApp(v___x_553_);
                    if v___x_554_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_553_);
                        crate::leanh::lean_dec_ref(v_arg_552_);
                        v___x_555_ = crate::leanh::lean_box(0);
                        return v___x_555_;
                    } else {
                        v_arg_556_ = crate::leanh::lean_ctor_get(v___x_553_, 1);
                        crate::leanh::lean_inc_ref(v_arg_556_);
                        v___x_557_ = l_Lean_Expr_appFnCleanup___redArg(v___x_553_);
                        v___x_558_ = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1;
                        v___x_559_ = l_Lean_Expr_isConstOf(v___x_557_, v___x_558_);
                        if v___x_559_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_552_);
                            v___x_560_ = l_Lean_Expr_isApp(v___x_557_);
                            if v___x_560_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_557_);
                                crate::leanh::lean_dec_ref(v_arg_556_);
                                v___x_561_ = crate::leanh::lean_box(0);
                                return v___x_561_;
                            } else {
                                v_arg_562_ = crate::leanh::lean_ctor_get(v___x_557_, 1);
                                crate::leanh::lean_inc_ref(v_arg_562_);
                                v___x_563_ = l_Lean_Expr_appFnCleanup___redArg(v___x_557_);
                                v___x_564_ = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
                                v___x_565_ = l_Lean_Expr_isConstOf(v___x_563_, v___x_564_);
                                if v___x_565_ == 0 {
                                    v___x_566_ = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3;
                                    v___x_567_ = l_Lean_Expr_isConstOf(v___x_563_, v___x_566_);
                                    crate::leanh::lean_dec_ref(v___x_563_);
                                    if v___x_567_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_562_);
                                        crate::leanh::lean_dec_ref(v_arg_556_);
                                        v___x_568_ = crate::leanh::lean_box(0);
                                        return v___x_568_;
                                    } else {
                                        v_nExpr_532_ = v_arg_562_;
                                        v_vExpr_533_ = v_arg_556_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_563_);
                                    v___x_569_ = l_Lean_Expr_cleanupAnnotations(v_arg_562_);
                                    v___x_570_ = l_Lean_Expr_isApp(v___x_569_);
                                    if v___x_570_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_569_);
                                        crate::leanh::lean_dec_ref(v_arg_556_);
                                        v___x_571_ = crate::leanh::lean_box(0);
                                        return v___x_571_;
                                    } else {
                                        v_arg_572_ = crate::leanh::lean_ctor_get(v___x_569_, 1);
                                        crate::leanh::lean_inc_ref(v_arg_572_);
                                        v___x_573_ = l_Lean_Expr_appFnCleanup___redArg(v___x_569_);
                                        v___x_574_ = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4;
                                        v___x_575_ = l_Lean_Expr_isConstOf(v___x_573_, v___x_574_);
                                        crate::leanh::lean_dec_ref(v___x_573_);
                                        if v___x_575_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_572_);
                                            crate::leanh::lean_dec_ref(v_arg_556_);
                                            v___x_576_ = crate::leanh::lean_box(0);
                                            return v___x_576_;
                                        } else {
                                            v___x_577_ =
                                                l_Lean_Meta_Sym_getNatValue_x3f(v_arg_572_);
                                            if crate::leanh::lean_obj_tag(v___x_577_) == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_556_);
                                                v___x_578_ = crate::leanh::lean_box(0);
                                                return v___x_578_;
                                            } else {
                                                if crate::leanh::lean_obj_tag(v_arg_556_) == 9 {
                                                    v_a_579_ =
                                                        crate::leanh::lean_ctor_get(v_arg_556_, 0);
                                                    crate::leanh::lean_inc_ref(v_a_579_);
                                                    crate::leanh::lean_dec_ref_known(v_arg_556_, 1);
                                                    if crate::leanh::lean_obj_tag(v_a_579_) == 0 {
                                                        v_val_580_ = crate::leanh::lean_ctor_get(
                                                            v___x_577_, 0,
                                                        );
                                                        v_isSharedCheck_590_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_577_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_590_ == 0 {
                                                            v___x_582_ = v___x_577_;
                                                            v_isShared_583_ = v_isSharedCheck_590_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_val_580_);
                                                            crate::leanh::lean_dec(v___x_577_);
                                                            v___x_582_ = crate::leanh::lean_box(0);
                                                            v_isShared_583_ = v_isSharedCheck_590_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_a_579_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_577_, 1,
                                                        );
                                                        v___x_591_ = crate::leanh::lean_box(0);
                                                        return v___x_591_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref_known(v___x_577_, 1);
                                                    crate::leanh::lean_dec_ref(v_arg_556_);
                                                    v___x_592_ = crate::leanh::lean_box(0);
                                                    return v___x_592_;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_557_);
                            v_nExpr_532_ = v_arg_556_;
                            v_vExpr_533_ = v_arg_552_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_534_ = l_Lean_Meta_Sym_getNatValue_x3f(v_nExpr_532_);
                if crate::leanh::lean_obj_tag(v___x_534_) == 0 {
                    crate::leanh::lean_dec_ref(v_vExpr_533_);
                    v___x_535_ = crate::leanh::lean_box(0);
                    return v___x_535_;
                } else {
                    v_val_536_ = crate::leanh::lean_ctor_get(v___x_534_, 0);
                    crate::leanh::lean_inc(v_val_536_);
                    crate::leanh::lean_dec_ref_known(v___x_534_, 1);
                    v___x_537_ = l_Lean_Meta_Sym_getNatValue_x3f(v_vExpr_533_);
                    if crate::leanh::lean_obj_tag(v___x_537_) == 0 {
                        crate::leanh::lean_dec(v_val_536_);
                        v___x_538_ = crate::leanh::lean_box(0);
                        return v___x_538_;
                    } else {
                        v_val_539_ = crate::leanh::lean_ctor_get(v___x_537_, 0);
                        v_isSharedCheck_548_ = (!crate::leanh::lean_is_exclusive(v___x_537_)) as u8;
                        if v_isSharedCheck_548_ == 0 {
                            v___x_541_ = v___x_537_;
                            v_isShared_542_ = v_isSharedCheck_548_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_539_);
                            crate::leanh::lean_dec(v___x_537_);
                            v___x_541_ = crate::leanh::lean_box(0);
                            v_isShared_542_ = v_isSharedCheck_548_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_543_ = l_BitVec_ofNat(v_val_536_, v_val_539_);
                crate::leanh::lean_dec(v_val_539_);
                v___x_544_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_544_, 0, v_val_536_);
                crate::leanh::lean_ctor_set(v___x_544_, 1, v___x_543_);
                if v_isShared_542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_541_, 0, v___x_544_);
                    v___x_546_ = v___x_541_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
                    v___x_546_ = v_reuseFailAlloc_547_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_546_;
            }
            4 => {
                v_val_584_ = crate::leanh::lean_ctor_get(v_a_579_, 0);
                crate::leanh::lean_inc(v_val_584_);
                crate::leanh::lean_dec_ref_known(v_a_579_, 1);
                v___x_585_ = l_BitVec_ofNat(v_val_580_, v_val_584_);
                crate::leanh::lean_dec(v_val_584_);
                v___x_586_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_586_, 0, v_val_580_);
                crate::leanh::lean_ctor_set(v___x_586_, 1, v___x_585_);
                if v_isShared_583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_582_, 0, v___x_586_);
                    v___x_588_ = v___x_582_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
                    v___x_588_ = v_reuseFailAlloc_589_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getUInt8Value_x3f(
    mut v_e_593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___x_600_: u8 = 0;
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_594_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_593_);
                if crate::leanh::lean_obj_tag(v___x_594_) == 0 {
                    v___x_595_ = crate::leanh::lean_box(0);
                    return v___x_595_;
                } else {
                    v_val_596_ = crate::leanh::lean_ctor_get(v___x_594_, 0);
                    v_isSharedCheck_605_ = (!crate::leanh::lean_is_exclusive(v___x_594_)) as u8;
                    if v_isSharedCheck_605_ == 0 {
                        v___x_598_ = v___x_594_;
                        v_isShared_599_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_596_);
                        crate::leanh::lean_dec(v___x_594_);
                        v___x_598_ = crate::leanh::lean_box(0);
                        v_isShared_599_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_600_ = lean_uint8_of_nat(v_val_596_);
                crate::leanh::lean_dec(v_val_596_);
                v___x_601_ = crate::leanh::lean_box((v___x_600_) as usize);
                if v_isShared_599_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_598_, 0, v___x_601_);
                    v___x_603_ = v___x_598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
                    v___x_603_ = v_reuseFailAlloc_604_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getUInt16Value_x3f(
    mut v_e_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_613_: u16 = 0;
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_607_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_606_);
                if crate::leanh::lean_obj_tag(v___x_607_) == 0 {
                    v___x_608_ = crate::leanh::lean_box(0);
                    return v___x_608_;
                } else {
                    v_val_609_ = crate::leanh::lean_ctor_get(v___x_607_, 0);
                    v_isSharedCheck_618_ = (!crate::leanh::lean_is_exclusive(v___x_607_)) as u8;
                    if v_isSharedCheck_618_ == 0 {
                        v___x_611_ = v___x_607_;
                        v_isShared_612_ = v_isSharedCheck_618_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_609_);
                        crate::leanh::lean_dec(v___x_607_);
                        v___x_611_ = crate::leanh::lean_box(0);
                        v_isShared_612_ = v_isSharedCheck_618_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_613_ = lean_uint16_of_nat(v_val_609_);
                crate::leanh::lean_dec(v_val_609_);
                v___x_614_ = crate::leanh::lean_box((v___x_613_) as usize);
                if v_isShared_612_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_611_, 0, v___x_614_);
                    v___x_616_ = v___x_611_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
                    v___x_616_ = v_reuseFailAlloc_617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getUInt32Value_x3f(
    mut v_e_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_625_: u8 = 0;
    let mut v___x_626_: u32 = 0;
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_620_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_619_);
                if crate::leanh::lean_obj_tag(v___x_620_) == 0 {
                    v___x_621_ = crate::leanh::lean_box(0);
                    return v___x_621_;
                } else {
                    v_val_622_ = crate::leanh::lean_ctor_get(v___x_620_, 0);
                    v_isSharedCheck_631_ = (!crate::leanh::lean_is_exclusive(v___x_620_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_624_ = v___x_620_;
                        v_isShared_625_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_622_);
                        crate::leanh::lean_dec(v___x_620_);
                        v___x_624_ = crate::leanh::lean_box(0);
                        v_isShared_625_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_626_ = lean_uint32_of_nat(v_val_622_);
                crate::leanh::lean_dec(v_val_622_);
                v___x_627_ = crate::leanh::lean_box_uint32(v___x_626_);
                if v_isShared_625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_624_, 0, v___x_627_);
                    v___x_629_ = v___x_624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
                    v___x_629_ = v_reuseFailAlloc_630_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getUInt64Value_x3f(
    mut v_e_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: u64 = 0;
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_633_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_632_);
                if crate::leanh::lean_obj_tag(v___x_633_) == 0 {
                    v___x_634_ = crate::leanh::lean_box(0);
                    return v___x_634_;
                } else {
                    v_val_635_ = crate::leanh::lean_ctor_get(v___x_633_, 0);
                    v_isSharedCheck_644_ = (!crate::leanh::lean_is_exclusive(v___x_633_)) as u8;
                    if v_isSharedCheck_644_ == 0 {
                        v___x_637_ = v___x_633_;
                        v_isShared_638_ = v_isSharedCheck_644_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_635_);
                        crate::leanh::lean_dec(v___x_633_);
                        v___x_637_ = crate::leanh::lean_box(0);
                        v_isShared_638_ = v_isSharedCheck_644_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_639_ = lean_uint64_of_nat(v_val_635_);
                crate::leanh::lean_dec(v_val_635_);
                v___x_640_ = crate::leanh::lean_box_uint64(v___x_639_);
                if v_isShared_638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_640_);
                    v___x_642_ = v___x_637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
                    v___x_642_ = v_reuseFailAlloc_643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getInt8Value_x3f(
    mut v_e_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_651_: u8 = 0;
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_646_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_645_);
                if crate::leanh::lean_obj_tag(v___x_646_) == 0 {
                    v___x_647_ = crate::leanh::lean_box(0);
                    return v___x_647_;
                } else {
                    v_val_648_ = crate::leanh::lean_ctor_get(v___x_646_, 0);
                    v_isSharedCheck_657_ = (!crate::leanh::lean_is_exclusive(v___x_646_)) as u8;
                    if v_isSharedCheck_657_ == 0 {
                        v___x_650_ = v___x_646_;
                        v_isShared_651_ = v_isSharedCheck_657_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_648_);
                        crate::leanh::lean_dec(v___x_646_);
                        v___x_650_ = crate::leanh::lean_box(0);
                        v_isShared_651_ = v_isSharedCheck_657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_652_ = lean_int8_of_int(v_val_648_);
                crate::leanh::lean_dec(v_val_648_);
                v___x_653_ = crate::leanh::lean_box((v___x_652_) as usize);
                if v_isShared_651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_650_, 0, v___x_653_);
                    v___x_655_ = v___x_650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
                    v___x_655_ = v_reuseFailAlloc_656_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_655_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getInt16Value_x3f(
    mut v_e_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_664_: u8 = 0;
    let mut v___x_665_: u16 = 0;
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_659_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_658_);
                if crate::leanh::lean_obj_tag(v___x_659_) == 0 {
                    v___x_660_ = crate::leanh::lean_box(0);
                    return v___x_660_;
                } else {
                    v_val_661_ = crate::leanh::lean_ctor_get(v___x_659_, 0);
                    v_isSharedCheck_670_ = (!crate::leanh::lean_is_exclusive(v___x_659_)) as u8;
                    if v_isSharedCheck_670_ == 0 {
                        v___x_663_ = v___x_659_;
                        v_isShared_664_ = v_isSharedCheck_670_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_661_);
                        crate::leanh::lean_dec(v___x_659_);
                        v___x_663_ = crate::leanh::lean_box(0);
                        v_isShared_664_ = v_isSharedCheck_670_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_665_ = lean_int16_of_int(v_val_661_);
                crate::leanh::lean_dec(v_val_661_);
                v___x_666_ = crate::leanh::lean_box((v___x_665_) as usize);
                if v_isShared_664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_663_, 0, v___x_666_);
                    v___x_668_ = v___x_663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
                    v___x_668_ = v_reuseFailAlloc_669_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getInt32Value_x3f(
    mut v_e_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_678_: u32 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_672_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_671_);
                if crate::leanh::lean_obj_tag(v___x_672_) == 0 {
                    v___x_673_ = crate::leanh::lean_box(0);
                    return v___x_673_;
                } else {
                    v_val_674_ = crate::leanh::lean_ctor_get(v___x_672_, 0);
                    v_isSharedCheck_683_ = (!crate::leanh::lean_is_exclusive(v___x_672_)) as u8;
                    if v_isSharedCheck_683_ == 0 {
                        v___x_676_ = v___x_672_;
                        v_isShared_677_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_674_);
                        crate::leanh::lean_dec(v___x_672_);
                        v___x_676_ = crate::leanh::lean_box(0);
                        v_isShared_677_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_678_ = lean_int32_of_int(v_val_674_);
                crate::leanh::lean_dec(v_val_674_);
                v___x_679_ = crate::leanh::lean_box_uint32(v___x_678_);
                if v_isShared_677_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_679_);
                    v___x_681_ = v___x_676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
                    v___x_681_ = v_reuseFailAlloc_682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getInt64Value_x3f(
    mut v_e_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_691_: u64 = 0;
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_685_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_684_);
                if crate::leanh::lean_obj_tag(v___x_685_) == 0 {
                    v___x_686_ = crate::leanh::lean_box(0);
                    return v___x_686_;
                } else {
                    v_val_687_ = crate::leanh::lean_ctor_get(v___x_685_, 0);
                    v_isSharedCheck_696_ = (!crate::leanh::lean_is_exclusive(v___x_685_)) as u8;
                    if v_isSharedCheck_696_ == 0 {
                        v___x_689_ = v___x_685_;
                        v_isShared_690_ = v_isSharedCheck_696_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_687_);
                        crate::leanh::lean_dec(v___x_685_);
                        v___x_689_ = crate::leanh::lean_box(0);
                        v_isShared_690_ = v_isSharedCheck_696_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_691_ = lean_int64_of_int(v_val_687_);
                crate::leanh::lean_dec(v_val_687_);
                v___x_692_ = crate::leanh::lean_box_uint64(v___x_691_);
                if v_isShared_690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_689_, 0, v___x_692_);
                    v___x_694_ = v___x_689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_695_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
                    v___x_694_ = v_reuseFailAlloc_695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getFinValue_x3f(
    mut v_e_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u8 = 0;
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: u8 = 0;
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u8 = 0;
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v_val_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_701_ = l_Lean_Expr_cleanupAnnotations(v_e_700_);
                v___x_702_ = l_Lean_Expr_isApp(v___x_701_);
                if v___x_702_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_701_);
                    v___x_703_ = crate::leanh::lean_box(0);
                    return v___x_703_;
                } else {
                    v___x_704_ = l_Lean_Expr_appFnCleanup___redArg(v___x_701_);
                    v___x_705_ = l_Lean_Expr_isApp(v___x_704_);
                    if v___x_705_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_704_);
                        v___x_706_ = crate::leanh::lean_box(0);
                        return v___x_706_;
                    } else {
                        v_arg_707_ = crate::leanh::lean_ctor_get(v___x_704_, 1);
                        crate::leanh::lean_inc_ref(v_arg_707_);
                        v___x_708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_704_);
                        v___x_709_ = l_Lean_Expr_isApp(v___x_708_);
                        if v___x_709_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_708_);
                            crate::leanh::lean_dec_ref(v_arg_707_);
                            v___x_710_ = crate::leanh::lean_box(0);
                            return v___x_710_;
                        } else {
                            v_arg_711_ = crate::leanh::lean_ctor_get(v___x_708_, 1);
                            crate::leanh::lean_inc_ref(v_arg_711_);
                            v___x_712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_708_);
                            v___x_713_ = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
                            v___x_714_ = l_Lean_Expr_isConstOf(v___x_712_, v___x_713_);
                            crate::leanh::lean_dec_ref(v___x_712_);
                            if v___x_714_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_711_);
                                crate::leanh::lean_dec_ref(v_arg_707_);
                                v___x_715_ = crate::leanh::lean_box(0);
                                return v___x_715_;
                            } else {
                                v___x_716_ = l_Lean_Expr_cleanupAnnotations(v_arg_711_);
                                v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
                                if v___x_717_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_716_);
                                    crate::leanh::lean_dec_ref(v_arg_707_);
                                    v___x_718_ = crate::leanh::lean_box(0);
                                    return v___x_718_;
                                } else {
                                    v_arg_719_ = crate::leanh::lean_ctor_get(v___x_716_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_719_);
                                    v___x_720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
                                    v___x_721_ = l_Lean_Meta_Sym_getFinValue_x3f___closed__1;
                                    v___x_722_ = l_Lean_Expr_isConstOf(v___x_720_, v___x_721_);
                                    crate::leanh::lean_dec_ref(v___x_720_);
                                    if v___x_722_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_719_);
                                        crate::leanh::lean_dec_ref(v_arg_707_);
                                        v___x_723_ = crate::leanh::lean_box(0);
                                        return v___x_723_;
                                    } else {
                                        v___x_724_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_719_);
                                        if crate::leanh::lean_obj_tag(v___x_724_) == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_707_);
                                            v___x_725_ = crate::leanh::lean_box(0);
                                            return v___x_725_;
                                        } else {
                                            if crate::leanh::lean_obj_tag(v_arg_707_) == 9 {
                                                v_a_726_ =
                                                    crate::leanh::lean_ctor_get(v_arg_707_, 0);
                                                crate::leanh::lean_inc_ref(v_a_726_);
                                                crate::leanh::lean_dec_ref_known(v_arg_707_, 1);
                                                if crate::leanh::lean_obj_tag(v_a_726_) == 0 {
                                                    v_val_727_ =
                                                        crate::leanh::lean_ctor_get(v___x_724_, 0);
                                                    v_isSharedCheck_740_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_724_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_740_ == 0 {
                                                        v___x_729_ = v___x_724_;
                                                        v_isShared_730_ = v_isSharedCheck_740_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_val_727_);
                                                        crate::leanh::lean_dec(v___x_724_);
                                                        v___x_729_ = crate::leanh::lean_box(0);
                                                        v_isShared_730_ = v_isSharedCheck_740_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_a_726_);
                                                    crate::leanh::lean_dec_ref_known(v___x_724_, 1);
                                                    v___x_741_ = crate::leanh::lean_box(0);
                                                    return v___x_741_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v___x_724_, 1);
                                                crate::leanh::lean_dec_ref(v_arg_707_);
                                                v___x_742_ = crate::leanh::lean_box(0);
                                                return v___x_742_;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_val_731_ = crate::leanh::lean_ctor_get(v_a_726_, 0);
                crate::leanh::lean_inc(v_val_731_);
                crate::leanh::lean_dec_ref_known(v_a_726_, 1);
                v___x_732_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_733_ = lean_nat_dec_eq(v_val_727_, v___x_732_);
                if v___x_733_ == 0 {
                    v___x_734_ = lean_nat_mod(v_val_731_, v_val_727_);
                    crate::leanh::lean_dec(v_val_731_);
                    v___x_735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_735_, 0, v_val_727_);
                    crate::leanh::lean_ctor_set(v___x_735_, 1, v___x_734_);
                    if v_isShared_730_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_729_, 0, v___x_735_);
                        v___x_737_ = v___x_729_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
                        v___x_737_ = v_reuseFailAlloc_738_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_731_);
                    crate::leanh::lean_del_object(v___x_729_);
                    crate::leanh::lean_dec(v_val_727_);
                    v___x_739_ = crate::leanh::lean_box(0);
                    return v___x_739_;
                }
            }
            2 => {
                return v___x_737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getCharValue_x3f(
    mut v_e_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: u8 = 0;
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_760_: u8 = 0;
    let mut v___x_761_: u32 = 0;
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_748_ = l_Lean_Expr_cleanupAnnotations(v_e_747_);
                v___x_749_ = l_Lean_Expr_isApp(v___x_748_);
                if v___x_749_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_748_);
                    v___x_750_ = crate::leanh::lean_box(0);
                    return v___x_750_;
                } else {
                    v_arg_751_ = crate::leanh::lean_ctor_get(v___x_748_, 1);
                    crate::leanh::lean_inc_ref(v_arg_751_);
                    v___x_752_ = l_Lean_Expr_appFnCleanup___redArg(v___x_748_);
                    v___x_753_ = l_Lean_Meta_Sym_getCharValue_x3f___closed__1;
                    v___x_754_ = l_Lean_Expr_isConstOf(v___x_752_, v___x_753_);
                    crate::leanh::lean_dec_ref(v___x_752_);
                    if v___x_754_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_751_);
                        v___x_755_ = crate::leanh::lean_box(0);
                        return v___x_755_;
                    } else {
                        if crate::leanh::lean_obj_tag(v_arg_751_) == 9 {
                            v_a_756_ = crate::leanh::lean_ctor_get(v_arg_751_, 0);
                            crate::leanh::lean_inc_ref(v_a_756_);
                            crate::leanh::lean_dec_ref_known(v_arg_751_, 1);
                            if crate::leanh::lean_obj_tag(v_a_756_) == 0 {
                                v_val_757_ = crate::leanh::lean_ctor_get(v_a_756_, 0);
                                v_isSharedCheck_766_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_756_)) as u8;
                                if v_isSharedCheck_766_ == 0 {
                                    v___x_759_ = v_a_756_;
                                    v_isShared_760_ = v_isSharedCheck_766_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_757_);
                                    crate::leanh::lean_dec(v_a_756_);
                                    v___x_759_ = crate::leanh::lean_box(0);
                                    v_isShared_760_ = v_isSharedCheck_766_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_a_756_);
                                v___x_767_ = crate::leanh::lean_box(0);
                                return v___x_767_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_arg_751_);
                            v___x_768_ = crate::leanh::lean_box(0);
                            return v___x_768_;
                        }
                    }
                }
            }
            1 => {
                v___x_761_ = l_Char_ofNat(v_val_757_);
                crate::leanh::lean_dec(v_val_757_);
                v___x_762_ = crate::leanh::lean_box_uint32(v___x_761_);
                if v_isShared_760_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_759_, 1);
                    crate::leanh::lean_ctor_set(v___x_759_, 0, v___x_762_);
                    v___x_764_ = v___x_759_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
                    v___x_764_ = v_reuseFailAlloc_765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getStringValue_x3f(
    mut v_e_769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_774_: u8 = 0;
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_769_) == 9 {
                    v_a_770_ = crate::leanh::lean_ctor_get(v_e_769_, 0);
                    crate::leanh::lean_inc_ref(v_a_770_);
                    crate::leanh::lean_dec_ref_known(v_e_769_, 1);
                    if crate::leanh::lean_obj_tag(v_a_770_) == 1 {
                        v_val_771_ = crate::leanh::lean_ctor_get(v_a_770_, 0);
                        v_isSharedCheck_778_ = (!crate::leanh::lean_is_exclusive(v_a_770_)) as u8;
                        if v_isSharedCheck_778_ == 0 {
                            v___x_773_ = v_a_770_;
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_771_);
                            crate::leanh::lean_dec(v_a_770_);
                            v___x_773_ = crate::leanh::lean_box(0);
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_770_);
                        v___x_779_ = crate::leanh::lean_box(0);
                        return v___x_779_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_769_);
                    v___x_780_ = crate::leanh::lean_box(0);
                    return v___x_780_;
                }
            }
            1 => {
                if v_isShared_774_ == 0 {
                    v___x_776_ = v___x_773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 0, v_val_771_);
                    v___x_776_ = v_reuseFailAlloc_777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_776_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_LitValues(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_LitValues(
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
pub unsafe fn initialize_Lean_Meta_Sym_LitValues(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_LitValues(builtin);
}
