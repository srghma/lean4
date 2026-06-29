// Lean compiler output
// Module: Lean.Meta.LitValues
// Imports: Lean.Meta.Basic Init.While
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_div, l_Rat_neg, l_Rat_ofInt};
use crate::r#gen::Init::Prelude::{l_BitVec_ofNat, l_Char_ofNat};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_const___override, l_Lean_Expr_consumeMData,
    l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_eagerReflBoolTrue, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkNatLit, l_Lean_mkRawNatLit, l_Lean_mkStrLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_whnfD,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprInt_mkNat;
use crate::ffi::{
    lean_int_add, lean_int_dec_le, lean_int_dec_lt, lean_int_neg, lean_nat_to_int,
};
use crate::ffi::{
    lean_uint8_to_nat, lean_uint16_of_nat, lean_uint16_to_nat, lean_uint32_of_nat,
    lean_uint64_of_nat, lean_uint64_to_nat,
};
use crate::ffi::{
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_mod, lean_nat_sub, lean_uint8_of_nat,
    lean_uint32_to_nat,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_Meta_getOfNatValue_x3f___closed__0_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Lean_Meta_getOfNatValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getOfNatValue_x3f___closed__1_value: crate::leanh::LeanStringObject<6> =
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
static mut l_Lean_Meta_getOfNatValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getOfNatValue_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17636616155771105671 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_getOfNatValue_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15578568367168711682 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getOfNatValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getNatValue_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_getNatValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getNatValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getNatValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getNatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getNatValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getNatValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getIntValue_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_getIntValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getIntValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getIntValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getIntValue_x3f___closed__2_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Lean_Meta_getIntValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getIntValue_x3f___closed__3_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Lean_Meta_getIntValue_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getIntValue_x3f___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__2_value)
                as *mut crate::leanh::LeanObject,
            9626815015619986526 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_getIntValue_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__3_value)
                as *mut crate::leanh::LeanObject,
            17185717442815859305 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getIntValue_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 97, 116, 0]};
static mut l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__0_value) as *mut crate::leanh::LeanObject,3708748166848919527 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getRatValue_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Meta_getRatValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getRatValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getRatValue_x3f___closed__1_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Meta_getRatValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getRatValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getRatValue_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getRatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11858238400308895562 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_getRatValue_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getRatValue_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getRatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            6100819061652633370 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getRatValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getRatValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getCharValue_x3f___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Meta_getCharValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getCharValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getCharValue_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getCharValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14164462494711235346 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_getCharValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getCharValue_x3f___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            18098914779984442139 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getCharValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getCharValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getFinValue_x3f___closed__0_value: crate::leanh::LeanStringObject<4> =
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
static mut l_Lean_Meta_getFinValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFinValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getFinValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getFinValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15815496672699636542 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getFinValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFinValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getBitVecValue_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Meta_getBitVecValue_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getBitVecValue_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getBitVecValue_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getBitVecValue_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_getBitVecValue_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            7578295756008745317 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getBitVecValue_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getBitVecValue_x3f___closed__3_value: crate::leanh::LeanStringObject<8> =
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
static mut l_Lean_Meta_getBitVecValue_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getBitVecValue_x3f___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5394957827732845164 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_getBitVecValue_x3f___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__3_value)
                as *mut crate::leanh::LeanObject,
            2059920148364733515 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getBitVecValue_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getBitVecValue_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt8Value_x3f___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [85, 73, 110, 116, 56, 0],
    };
static mut l_Lean_Meta_getUInt8Value_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt8Value_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt8Value_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt8Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15764114953608429200 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getUInt8Value_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt8Value_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt16Value_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [85, 73, 110, 116, 49, 54, 0],
    };
static mut l_Lean_Meta_getUInt16Value_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt16Value_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt16Value_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt16Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9755723410228041222 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getUInt16Value_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt16Value_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt32Value_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [85, 73, 110, 116, 51, 50, 0],
    };
static mut l_Lean_Meta_getUInt32Value_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt32Value_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt32Value_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt32Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13474504806189678690 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getUInt32Value_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt32Value_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt64Value_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [85, 73, 110, 116, 54, 52, 0],
    };
static mut l_Lean_Meta_getUInt64Value_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt64Value_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getUInt64Value_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt64Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2954612489107370298 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getUInt64Value_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getUInt64Value_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_normLitValue___closed__5_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_normLitValue___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_normLitValue___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_normLitValue___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__5_value)
                as *mut crate::leanh::LeanObject,
            6362876895233142233 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_normLitValue___closed__10_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_normLitValue___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_normLitValue___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getFinValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15815496672699636542 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_normLitValue___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__10_value)
                as *mut crate::leanh::LeanObject,
            6045136802442138716 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_normLitValue___closed__13_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            105, 110, 115, 116, 78, 101, 90, 101, 114, 111, 83, 117, 99, 99, 0,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_normLitValue___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getNatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_normLitValue___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__14_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__13_value)
                as *mut crate::leanh::LeanObject,
            10810852250111692195 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_normLitValue___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt8Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15764114953608429200 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_normLitValue___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__19_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__10_value)
                as *mut crate::leanh::LeanObject,
            1458943469631247978 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_normLitValue___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt16Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9755723410228041222 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_normLitValue___closed__22_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__22_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__10_value)
                as *mut crate::leanh::LeanObject,
            16668572274245391716 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__22_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_normLitValue___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt32Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            13474504806189678690 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_normLitValue___closed__25_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__25_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__10_value)
                as *mut crate::leanh::LeanObject,
            16173759620455419504 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_normLitValue___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Meta_normLitValue___closed__28_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getUInt64Value_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2954612489107370298 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_normLitValue___closed__28_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__28_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__10_value)
                as *mut crate::leanh::LeanObject,
            532958730868083720 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_normLitValue___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_normLitValue___closed__28_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_normLitValue___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_normLitValue___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 117, 99, 99, 0],
    };
static mut l_Lean_Meta_litToCtor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_litToCtor___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getNatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_litToCtor___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16112798088292836701 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [122, 101, 114, 111, 0],
    };
static mut l_Lean_Meta_litToCtor___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_litToCtor___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getNatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_litToCtor___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__3_value)
                as *mut crate::leanh::LeanObject,
            13428217069302927667 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static l_Lean_Meta_litToCtor___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_litToCtor___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__6_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getOfNatValue_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            6667203625087222464 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__8_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [110, 101, 103, 83, 117, 99, 99, 0],
    };
static mut l_Lean_Meta_litToCtor___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__8_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_litToCtor___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getIntValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            7009148538150066493 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_litToCtor___closed__9_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__8_value)
                as *mut crate::leanh::LeanObject,
            14511501467246783669 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_litToCtor___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__12_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [76, 84, 0],
    };
static mut l_Lean_Meta_litToCtor___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_litToCtor___closed__13_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [108, 116, 0],
    };
static mut l_Lean_Meta_litToCtor___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__13_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_litToCtor___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__12_value)
                as *mut crate::leanh::LeanObject,
            17878876274162330439 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_litToCtor___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__14_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__13_value)
                as *mut crate::leanh::LeanObject,
            11833570877100518198 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_litToCtor___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__17_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_litToCtor___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_litToCtor___closed__18_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__17_value)
                as *mut crate::leanh::LeanObject,
            14651840373392481165 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__20_value: crate::leanh::LeanStringObject<18> =
    crate::leanh::LeanStringObject {
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
            111, 102, 95, 100, 101, 99, 105, 100, 101, 95, 101, 113, 95, 116, 114, 117, 101, 0,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_litToCtor___closed__21_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__20_value)
                as *mut crate::leanh::LeanObject,
            1819210885479960519 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__23_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [100, 101, 99, 76, 116, 0],
    };
static mut l_Lean_Meta_litToCtor___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__23_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_litToCtor___closed__24_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getNatValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11442535297760353691 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_litToCtor___closed__24_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__24_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__23_value)
                as *mut crate::leanh::LeanObject,
            12899256189766038598 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__24_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_litToCtor___closed__26_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [109, 107, 0],
    };
static mut l_Lean_Meta_litToCtor___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__26_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_litToCtor___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getFinValue_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            15815496672699636542 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_litToCtor___closed__27_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__27_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__26_value)
                as *mut crate::leanh::LeanObject,
            5825593324384481310 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_litToCtor___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_litToCtor___closed__27_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_litToCtor___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_litToCtor___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 105, 115, 116, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 105, 108, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,18135193680607614554 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 115, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__3_value) as *mut crate::leanh::LeanObject,8614124190858717794 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getListLitOf_x3f___redArg___closed__0_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_getListLitOf_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getListLitOf_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getListLit_x3f___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_getListLit_x3f___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_getListLit_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getListLit_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value:
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
    m_data: [116, 111, 65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,9582258842178272501 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8414467900391110369 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_getRawNatValue_x3f(
    mut v_e_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2151_: u8 = 0;
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2146_ = l_Lean_Expr_consumeMData(v_e_2145_);
                if crate::leanh::lean_obj_tag(v___x_2146_) == 9 {
                    v_a_2147_ = crate::leanh::lean_ctor_get(v___x_2146_, 0);
                    crate::leanh::lean_inc_ref(v_a_2147_);
                    crate::leanh::lean_dec_ref_known(v___x_2146_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2147_) == 0 {
                        v_val_2148_ = crate::leanh::lean_ctor_get(v_a_2147_, 0);
                        v_isSharedCheck_2155_ = (!crate::leanh::lean_is_exclusive(v_a_2147_)) as u8;
                        if v_isSharedCheck_2155_ == 0 {
                            v___x_2150_ = v_a_2147_;
                            v_isShared_2151_ = v_isSharedCheck_2155_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2148_);
                            crate::leanh::lean_dec(v_a_2147_);
                            v___x_2150_ = crate::leanh::lean_box(0);
                            v_isShared_2151_ = v_isSharedCheck_2155_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2147_);
                        v___x_2156_ = crate::leanh::lean_box(0);
                        return v___x_2156_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2146_);
                    v___x_2157_ = crate::leanh::lean_box(0);
                    return v___x_2157_;
                }
            }
            1 => {
                if v_isShared_2151_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2150_, 1);
                    v___x_2153_ = v___x_2150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_val_2148_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getRawNatValue_x3f___boxed(
    mut v_e_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Lean_Meta_getRawNatValue_x3f(v_e_2158_);
    crate::leanh::lean_dec_ref(v_e_2158_);
    return v_res_2159_;
}
pub unsafe fn l_Lean_Meta_getOfNatValue_x3f(
    mut v_e_2165_: *mut crate::leanh::LeanObject,
    mut v_typeDeclName_2166_: *mut crate::leanh::LeanObject,
    mut v_a_2167_: *mut crate::leanh::LeanObject,
    mut v_a_2168_: *mut crate::leanh::LeanObject,
    mut v_a_2169_: *mut crate::leanh::LeanObject,
    mut v_a_2170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: u8 = 0;
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: u8 = 0;
    let mut v_arg_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: u8 = 0;
    let mut v_arg_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2220_: u8 = 0;
    let mut v_isSharedCheck_2221_: u8 = 0;
    let mut v_a_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2229_: u8 = 0;
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut v_a_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2175_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2165_, v_a_2168_);
                if crate::leanh::lean_obj_tag(v___x_2175_) == 0 {
                    v_a_2176_ = crate::leanh::lean_ctor_get(v___x_2175_, 0);
                    v_isSharedCheck_2230_ = (!crate::leanh::lean_is_exclusive(v___x_2175_)) as u8;
                    if v_isSharedCheck_2230_ == 0 {
                        v___x_2178_ = v___x_2175_;
                        v_isShared_2179_ = v_isSharedCheck_2230_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2176_);
                        crate::leanh::lean_dec(v___x_2175_);
                        v___x_2178_ = crate::leanh::lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2230_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2231_ = crate::leanh::lean_ctor_get(v___x_2175_, 0);
                    v_isSharedCheck_2238_ = (!crate::leanh::lean_is_exclusive(v___x_2175_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v___x_2233_ = v___x_2175_;
                        v_isShared_2234_ = v_isSharedCheck_2238_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2231_);
                        crate::leanh::lean_dec(v___x_2175_);
                        v___x_2233_ = crate::leanh::lean_box(0);
                        v_isShared_2234_ = v_isSharedCheck_2238_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2173_ = crate::leanh::lean_box(0);
                v___x_2174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2173_);
                return v___x_2174_;
            }
            2 => {
                v___x_2185_ = l_Lean_Expr_cleanupAnnotations(v_a_2176_);
                v___x_2186_ = l_Lean_Expr_isApp(v___x_2185_);
                if v___x_2186_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2185_);
                    state = 3;
                    continue;
                } else {
                    v___x_2187_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2185_);
                    v___x_2188_ = l_Lean_Expr_isApp(v___x_2187_);
                    if v___x_2188_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2187_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_2189_ = crate::leanh::lean_ctor_get(v___x_2187_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2189_);
                        v___x_2190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2187_);
                        v___x_2191_ = l_Lean_Expr_isApp(v___x_2190_);
                        if v___x_2191_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2190_);
                            crate::leanh::lean_dec_ref(v_arg_2189_);
                            state = 3;
                            continue;
                        } else {
                            v_arg_2192_ = crate::leanh::lean_ctor_get(v___x_2190_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2192_);
                            v___x_2193_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2190_);
                            v___x_2194_ = l_Lean_Meta_getOfNatValue_x3f___closed__2;
                            v___x_2195_ = l_Lean_Expr_isConstOf(v___x_2193_, v___x_2194_);
                            crate::leanh::lean_dec_ref(v___x_2193_);
                            if v___x_2195_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2192_);
                                crate::leanh::lean_dec_ref(v_arg_2189_);
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_2178_);
                                v___x_2196_ = l_Lean_Meta_whnfD(
                                    v_arg_2192_,
                                    v_a_2167_,
                                    v_a_2168_,
                                    v_a_2169_,
                                    v_a_2170_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2196_) == 0 {
                                    v_a_2197_ = crate::leanh::lean_ctor_get(v___x_2196_, 0);
                                    v_isSharedCheck_2221_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2196_)) as u8;
                                    if v_isSharedCheck_2221_ == 0 {
                                        v___x_2199_ = v___x_2196_;
                                        v_isShared_2200_ = v_isSharedCheck_2221_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2197_);
                                        crate::leanh::lean_dec(v___x_2196_);
                                        v___x_2199_ = crate::leanh::lean_box(0);
                                        v_isShared_2200_ = v_isSharedCheck_2221_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_2189_);
                                    v_a_2222_ = crate::leanh::lean_ctor_get(v___x_2196_, 0);
                                    v_isSharedCheck_2229_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2196_)) as u8;
                                    if v_isSharedCheck_2229_ == 0 {
                                        v___x_2224_ = v___x_2196_;
                                        v_isShared_2225_ = v_isSharedCheck_2229_;
                                        state = 10;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2222_);
                                        crate::leanh::lean_dec(v___x_2196_);
                                        v___x_2224_ = crate::leanh::lean_box(0);
                                        v_isShared_2225_ = v_isSharedCheck_2229_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_2181_ = crate::leanh::lean_box(0);
                if v_isShared_2179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2178_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                    v___x_2183_ = v_reuseFailAlloc_2184_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2183_;
            }
            5 => {
                v___x_2201_ = l_Lean_Expr_getAppFn(v_a_2197_);
                v___x_2202_ = l_Lean_Expr_isConstOf(v___x_2201_, v_typeDeclName_2166_);
                crate::leanh::lean_dec_ref(v___x_2201_);
                if v___x_2202_ == 0 {
                    crate::leanh::lean_dec(v_a_2197_);
                    crate::leanh::lean_dec_ref(v_arg_2189_);
                    v___x_2203_ = crate::leanh::lean_box(0);
                    if v_isShared_2200_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2203_);
                        v___x_2205_ = v___x_2199_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2206_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
                        v___x_2205_ = v_reuseFailAlloc_2206_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_2207_ = l_Lean_Expr_consumeMData(v_arg_2189_);
                    crate::leanh::lean_dec_ref(v_arg_2189_);
                    if crate::leanh::lean_obj_tag(v___x_2207_) == 9 {
                        v_a_2208_ = crate::leanh::lean_ctor_get(v___x_2207_, 0);
                        crate::leanh::lean_inc_ref(v_a_2208_);
                        crate::leanh::lean_dec_ref_known(v___x_2207_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2208_) == 0 {
                            v_val_2209_ = crate::leanh::lean_ctor_get(v_a_2208_, 0);
                            v_isSharedCheck_2220_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2208_)) as u8;
                            if v_isSharedCheck_2220_ == 0 {
                                v___x_2211_ = v_a_2208_;
                                v_isShared_2212_ = v_isSharedCheck_2220_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_2209_);
                                crate::leanh::lean_dec(v_a_2208_);
                                v___x_2211_ = crate::leanh::lean_box(0);
                                v_isShared_2212_ = v_isSharedCheck_2220_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_a_2208_);
                            crate::leanh::lean_del_object(v___x_2199_);
                            crate::leanh::lean_dec(v_a_2197_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2207_);
                        crate::leanh::lean_del_object(v___x_2199_);
                        crate::leanh::lean_dec(v_a_2197_);
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2205_;
            }
            7 => {
                v___x_2213_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2213_, 0, v_val_2209_);
                crate::leanh::lean_ctor_set(v___x_2213_, 1, v_a_2197_);
                if v_isShared_2212_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2211_, 1);
                    crate::leanh::lean_ctor_set(v___x_2211_, 0, v___x_2213_);
                    v___x_2215_ = v___x_2211_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2213_);
                    v___x_2215_ = v_reuseFailAlloc_2219_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2200_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2215_);
                    v___x_2217_ = v___x_2199_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
                    v___x_2217_ = v_reuseFailAlloc_2218_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2217_;
            }
            10 => {
                if v_isShared_2225_ == 0 {
                    v___x_2227_ = v___x_2224_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
                    v___x_2227_ = v_reuseFailAlloc_2228_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2227_;
            }
            12 => {
                if v_isShared_2234_ == 0 {
                    v___x_2236_ = v___x_2233_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2237_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
                    v___x_2236_ = v_reuseFailAlloc_2237_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2236_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getOfNatValue_x3f___boxed(
    mut v_e_2239_: *mut crate::leanh::LeanObject,
    mut v_typeDeclName_2240_: *mut crate::leanh::LeanObject,
    mut v_a_2241_: *mut crate::leanh::LeanObject,
    mut v_a_2242_: *mut crate::leanh::LeanObject,
    mut v_a_2243_: *mut crate::leanh::LeanObject,
    mut v_a_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2246_ = l_Lean_Meta_getOfNatValue_x3f(
        v_e_2239_,
        v_typeDeclName_2240_,
        v_a_2241_,
        v_a_2242_,
        v_a_2243_,
        v_a_2244_,
    );
    crate::leanh::lean_dec(v_a_2244_);
    crate::leanh::lean_dec_ref(v_a_2243_);
    crate::leanh::lean_dec(v_a_2242_);
    crate::leanh::lean_dec_ref(v_a_2241_);
    crate::leanh::lean_dec(v_typeDeclName_2240_);
    return v_res_2246_;
}
pub unsafe fn l_Lean_Meta_getNatValue_x3f(
    mut v_e_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v_val_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v_fst_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v_a_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_e_2256_ = l_Lean_Expr_consumeMData(v_e_2250_);
                v___x_2257_ = l_Lean_Meta_getRawNatValue_x3f(v_e_2256_);
                if crate::leanh::lean_obj_tag(v___x_2257_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_2256_);
                    v___x_2258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2258_, 0, v___x_2257_);
                    return v___x_2258_;
                } else {
                    crate::leanh::lean_dec(v___x_2257_);
                    v___x_2259_ = l_Lean_Meta_getNatValue_x3f___closed__1;
                    v___x_2260_ = l_Lean_Meta_getOfNatValue_x3f(
                        v_e_2256_,
                        v___x_2259_,
                        v_a_2251_,
                        v_a_2252_,
                        v_a_2253_,
                        v_a_2254_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2260_) == 0 {
                        v_a_2261_ = crate::leanh::lean_ctor_get(v___x_2260_, 0);
                        v_isSharedCheck_2281_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2260_)) as u8;
                        if v_isSharedCheck_2281_ == 0 {
                            v___x_2263_ = v___x_2260_;
                            v_isShared_2264_ = v_isSharedCheck_2281_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2261_);
                            crate::leanh::lean_dec(v___x_2260_);
                            v___x_2263_ = crate::leanh::lean_box(0);
                            v_isShared_2264_ = v_isSharedCheck_2281_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2282_ = crate::leanh::lean_ctor_get(v___x_2260_, 0);
                        v_isSharedCheck_2289_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2260_)) as u8;
                        if v_isSharedCheck_2289_ == 0 {
                            v___x_2284_ = v___x_2260_;
                            v_isShared_2285_ = v_isSharedCheck_2289_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2282_);
                            crate::leanh::lean_dec(v___x_2260_);
                            v___x_2284_ = crate::leanh::lean_box(0);
                            v_isShared_2285_ = v_isSharedCheck_2289_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2261_) == 1 {
                    v_val_2265_ = crate::leanh::lean_ctor_get(v_a_2261_, 0);
                    v_isSharedCheck_2276_ = (!crate::leanh::lean_is_exclusive(v_a_2261_)) as u8;
                    if v_isSharedCheck_2276_ == 0 {
                        v___x_2267_ = v_a_2261_;
                        v_isShared_2268_ = v_isSharedCheck_2276_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2265_);
                        crate::leanh::lean_dec(v_a_2261_);
                        v___x_2267_ = crate::leanh::lean_box(0);
                        v_isShared_2268_ = v_isSharedCheck_2276_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2261_);
                    v___x_2277_ = crate::leanh::lean_box(0);
                    if v_isShared_2264_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2263_, 0, v___x_2277_);
                        v___x_2279_ = v___x_2263_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
                        v___x_2279_ = v_reuseFailAlloc_2280_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_2269_ = crate::leanh::lean_ctor_get(v_val_2265_, 0);
                crate::leanh::lean_inc(v_fst_2269_);
                crate::leanh::lean_dec(v_val_2265_);
                if v_isShared_2268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2267_, 0, v_fst_2269_);
                    v___x_2271_ = v___x_2267_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_fst_2269_);
                    v___x_2271_ = v_reuseFailAlloc_2275_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2264_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2263_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2273_;
            }
            5 => {
                return v___x_2279_;
            }
            6 => {
                if v_isShared_2285_ == 0 {
                    v___x_2287_ = v___x_2284_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
                    v___x_2287_ = v_reuseFailAlloc_2288_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getNatValue_x3f___boxed(
    mut v_e_2290_: *mut crate::leanh::LeanObject,
    mut v_a_2291_: *mut crate::leanh::LeanObject,
    mut v_a_2292_: *mut crate::leanh::LeanObject,
    mut v_a_2293_: *mut crate::leanh::LeanObject,
    mut v_a_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2296_ =
        l_Lean_Meta_getNatValue_x3f(v_e_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
    crate::leanh::lean_dec(v_a_2294_);
    crate::leanh::lean_dec_ref(v_a_2293_);
    crate::leanh::lean_dec(v_a_2292_);
    crate::leanh::lean_dec_ref(v_a_2291_);
    crate::leanh::lean_dec_ref(v_e_2290_);
    return v_res_2296_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_getIntValue_x3f_spec__0(
    mut v_a_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = lean_nat_to_int(v_a_2297_);
    return v___x_2298_;
}
pub unsafe fn l_Lean_Meta_getIntValue_x3f(
    mut v_e_2307_: *mut crate::leanh::LeanObject,
    mut v_a_2308_: *mut crate::leanh::LeanObject,
    mut v_a_2309_: *mut crate::leanh::LeanObject,
    mut v_a_2310_: *mut crate::leanh::LeanObject,
    mut v_a_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2318_: u8 = 0;
    let mut v_val_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2322_: u8 = 0;
    let mut v_fst_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2336_: u8 = 0;
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v_arg_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: u8 = 0;
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v_val_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v_fst_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2375_: u8 = 0;
    let mut v_a_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2383_: u8 = 0;
    let mut v_isSharedCheck_2384_: u8 = 0;
    let mut v_a_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut v_isSharedCheck_2393_: u8 = 0;
    let mut v_a_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2397_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2313_ = l_Lean_Meta_getIntValue_x3f___closed__1;
                crate::leanh::lean_inc_ref(v_e_2307_);
                v___x_2314_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_2307_,
                    v___x_2313_,
                    v_a_2308_,
                    v_a_2309_,
                    v_a_2310_,
                    v_a_2311_,
                );
                if crate::leanh::lean_obj_tag(v___x_2314_) == 0 {
                    v_a_2315_ = crate::leanh::lean_ctor_get(v___x_2314_, 0);
                    v_isSharedCheck_2393_ = (!crate::leanh::lean_is_exclusive(v___x_2314_)) as u8;
                    if v_isSharedCheck_2393_ == 0 {
                        v___x_2317_ = v___x_2314_;
                        v_isShared_2318_ = v_isSharedCheck_2393_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2315_);
                        crate::leanh::lean_dec(v___x_2314_);
                        v___x_2317_ = crate::leanh::lean_box(0);
                        v_isShared_2318_ = v_isSharedCheck_2393_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2307_);
                    v_a_2394_ = crate::leanh::lean_ctor_get(v___x_2314_, 0);
                    v_isSharedCheck_2401_ = (!crate::leanh::lean_is_exclusive(v___x_2314_)) as u8;
                    if v_isSharedCheck_2401_ == 0 {
                        v___x_2396_ = v___x_2314_;
                        v_isShared_2397_ = v_isSharedCheck_2401_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2394_);
                        crate::leanh::lean_dec(v___x_2314_);
                        v___x_2396_ = crate::leanh::lean_box(0);
                        v_isShared_2397_ = v_isSharedCheck_2401_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2315_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_2307_);
                    v_val_2319_ = crate::leanh::lean_ctor_get(v_a_2315_, 0);
                    v_isSharedCheck_2331_ = (!crate::leanh::lean_is_exclusive(v_a_2315_)) as u8;
                    if v_isSharedCheck_2331_ == 0 {
                        v___x_2321_ = v_a_2315_;
                        v_isShared_2322_ = v_isSharedCheck_2331_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2319_);
                        crate::leanh::lean_dec(v_a_2315_);
                        v___x_2321_ = crate::leanh::lean_box(0);
                        v_isShared_2322_ = v_isSharedCheck_2331_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2317_);
                    crate::leanh::lean_dec(v_a_2315_);
                    v___x_2332_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2307_, v_a_2309_);
                    if crate::leanh::lean_obj_tag(v___x_2332_) == 0 {
                        v_a_2333_ = crate::leanh::lean_ctor_get(v___x_2332_, 0);
                        v_isSharedCheck_2384_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2332_)) as u8;
                        if v_isSharedCheck_2384_ == 0 {
                            v___x_2335_ = v___x_2332_;
                            v_isShared_2336_ = v_isSharedCheck_2384_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2333_);
                            crate::leanh::lean_dec(v___x_2332_);
                            v___x_2335_ = crate::leanh::lean_box(0);
                            v_isShared_2336_ = v_isSharedCheck_2384_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2385_ = crate::leanh::lean_ctor_get(v___x_2332_, 0);
                        v_isSharedCheck_2392_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2332_)) as u8;
                        if v_isSharedCheck_2392_ == 0 {
                            v___x_2387_ = v___x_2332_;
                            v_isShared_2388_ = v_isSharedCheck_2392_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2385_);
                            crate::leanh::lean_dec(v___x_2332_);
                            v___x_2387_ = crate::leanh::lean_box(0);
                            v_isShared_2388_ = v_isSharedCheck_2392_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_fst_2323_ = crate::leanh::lean_ctor_get(v_val_2319_, 0);
                crate::leanh::lean_inc(v_fst_2323_);
                crate::leanh::lean_dec(v_val_2319_);
                v___x_2324_ = lean_nat_to_int(v_fst_2323_);
                if v_isShared_2322_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2321_, 0, v___x_2324_);
                    v___x_2326_ = v___x_2321_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2324_);
                    v___x_2326_ = v_reuseFailAlloc_2330_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2318_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2317_, 0, v___x_2326_);
                    v___x_2328_ = v___x_2317_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
                    v___x_2328_ = v_reuseFailAlloc_2329_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2328_;
            }
            5 => {
                v___x_2342_ = l_Lean_Expr_cleanupAnnotations(v_a_2333_);
                v___x_2343_ = l_Lean_Expr_isApp(v___x_2342_);
                if v___x_2343_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2342_);
                    state = 6;
                    continue;
                } else {
                    v_arg_2344_ = crate::leanh::lean_ctor_get(v___x_2342_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2344_);
                    v___x_2345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2342_);
                    v___x_2346_ = l_Lean_Expr_isApp(v___x_2345_);
                    if v___x_2346_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2345_);
                        crate::leanh::lean_dec_ref(v_arg_2344_);
                        state = 6;
                        continue;
                    } else {
                        v___x_2347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2345_);
                        v___x_2348_ = l_Lean_Expr_isApp(v___x_2347_);
                        if v___x_2348_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2347_);
                            crate::leanh::lean_dec_ref(v_arg_2344_);
                            state = 6;
                            continue;
                        } else {
                            v___x_2349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2347_);
                            v___x_2350_ = l_Lean_Meta_getIntValue_x3f___closed__4;
                            v___x_2351_ = l_Lean_Expr_isConstOf(v___x_2349_, v___x_2350_);
                            crate::leanh::lean_dec_ref(v___x_2349_);
                            if v___x_2351_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2344_);
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_2335_);
                                v___x_2352_ = l_Lean_Meta_getOfNatValue_x3f(
                                    v_arg_2344_,
                                    v___x_2313_,
                                    v_a_2308_,
                                    v_a_2309_,
                                    v_a_2310_,
                                    v_a_2311_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2352_) == 0 {
                                    v_a_2353_ = crate::leanh::lean_ctor_get(v___x_2352_, 0);
                                    v_isSharedCheck_2375_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2352_)) as u8;
                                    if v_isSharedCheck_2375_ == 0 {
                                        v___x_2355_ = v___x_2352_;
                                        v_isShared_2356_ = v_isSharedCheck_2375_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2353_);
                                        crate::leanh::lean_dec(v___x_2352_);
                                        v___x_2355_ = crate::leanh::lean_box(0);
                                        v_isShared_2356_ = v_isSharedCheck_2375_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v_a_2376_ = crate::leanh::lean_ctor_get(v___x_2352_, 0);
                                    v_isSharedCheck_2383_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2352_)) as u8;
                                    if v_isSharedCheck_2383_ == 0 {
                                        v___x_2378_ = v___x_2352_;
                                        v_isShared_2379_ = v_isSharedCheck_2383_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2376_);
                                        crate::leanh::lean_dec(v___x_2352_);
                                        v___x_2378_ = crate::leanh::lean_box(0);
                                        v_isShared_2379_ = v_isSharedCheck_2383_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                v___x_2338_ = crate::leanh::lean_box(0);
                if v_isShared_2336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2338_);
                    v___x_2340_ = v___x_2335_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2341_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
                    v___x_2340_ = v_reuseFailAlloc_2341_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2340_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_2353_) == 1 {
                    v_val_2357_ = crate::leanh::lean_ctor_get(v_a_2353_, 0);
                    v_isSharedCheck_2370_ = (!crate::leanh::lean_is_exclusive(v_a_2353_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2359_ = v_a_2353_;
                        v_isShared_2360_ = v_isSharedCheck_2370_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2357_);
                        crate::leanh::lean_dec(v_a_2353_);
                        v___x_2359_ = crate::leanh::lean_box(0);
                        v_isShared_2360_ = v_isSharedCheck_2370_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2353_);
                    v___x_2371_ = crate::leanh::lean_box(0);
                    if v_isShared_2356_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2371_);
                        v___x_2373_ = v___x_2355_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2374_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
                        v___x_2373_ = v_reuseFailAlloc_2374_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                v_fst_2361_ = crate::leanh::lean_ctor_get(v_val_2357_, 0);
                crate::leanh::lean_inc(v_fst_2361_);
                crate::leanh::lean_dec(v_val_2357_);
                v___x_2362_ = lean_nat_to_int(v_fst_2361_);
                v___x_2363_ = lean_int_neg(v___x_2362_);
                crate::leanh::lean_dec(v___x_2362_);
                if v_isShared_2360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2359_, 0, v___x_2363_);
                    v___x_2365_ = v___x_2359_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2363_);
                    v___x_2365_ = v_reuseFailAlloc_2369_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2356_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2365_);
                    v___x_2367_ = v___x_2355_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
                    v___x_2367_ = v_reuseFailAlloc_2368_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2367_;
            }
            12 => {
                return v___x_2373_;
            }
            13 => {
                if v_isShared_2379_ == 0 {
                    v___x_2381_ = v___x_2378_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
                    v___x_2381_ = v_reuseFailAlloc_2382_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2381_;
            }
            15 => {
                if v_isShared_2388_ == 0 {
                    v___x_2390_ = v___x_2387_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
                    v___x_2390_ = v_reuseFailAlloc_2391_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2390_;
            }
            17 => {
                if v_isShared_2397_ == 0 {
                    v___x_2399_ = v___x_2396_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
                    v___x_2399_ = v_reuseFailAlloc_2400_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getIntValue_x3f___boxed(
    mut v_e_2402_: *mut crate::leanh::LeanObject,
    mut v_a_2403_: *mut crate::leanh::LeanObject,
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
    mut v_a_2406_: *mut crate::leanh::LeanObject,
    mut v_a_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ =
        l_Lean_Meta_getIntValue_x3f(v_e_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
    crate::leanh::lean_dec(v_a_2406_);
    crate::leanh::lean_dec_ref(v_a_2405_);
    crate::leanh::lean_dec(v_a_2404_);
    crate::leanh::lean_dec_ref(v_a_2403_);
    return v_res_2408_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(
    mut v_a_2409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2410_ = lean_nat_to_int(v_a_2409_);
    v___x_2411_ = l_Rat_ofInt(v___x_2410_);
    return v___x_2411_;
}
pub unsafe fn l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(
    mut v_e_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v_val_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2430_: u8 = 0;
    let mut v_fst_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2439_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2444_: u8 = 0;
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: u8 = 0;
    let mut v_arg_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2464_: u8 = 0;
    let mut v_val_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v_fst_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2478_: u8 = 0;
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut v_a_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_isSharedCheck_2492_: u8 = 0;
    let mut v_a_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2496_: u8 = 0;
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_a_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2421_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1;
                crate::leanh::lean_inc_ref(v_e_2415_);
                v___x_2422_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_2415_,
                    v___x_2421_,
                    v_a_2416_,
                    v_a_2417_,
                    v_a_2418_,
                    v_a_2419_,
                );
                if crate::leanh::lean_obj_tag(v___x_2422_) == 0 {
                    v_a_2423_ = crate::leanh::lean_ctor_get(v___x_2422_, 0);
                    v_isSharedCheck_2501_ = (!crate::leanh::lean_is_exclusive(v___x_2422_)) as u8;
                    if v_isSharedCheck_2501_ == 0 {
                        v___x_2425_ = v___x_2422_;
                        v_isShared_2426_ = v_isSharedCheck_2501_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2423_);
                        crate::leanh::lean_dec(v___x_2422_);
                        v___x_2425_ = crate::leanh::lean_box(0);
                        v_isShared_2426_ = v_isSharedCheck_2501_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2415_);
                    v_a_2502_ = crate::leanh::lean_ctor_get(v___x_2422_, 0);
                    v_isSharedCheck_2509_ = (!crate::leanh::lean_is_exclusive(v___x_2422_)) as u8;
                    if v_isSharedCheck_2509_ == 0 {
                        v___x_2504_ = v___x_2422_;
                        v_isShared_2505_ = v_isSharedCheck_2509_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2502_);
                        crate::leanh::lean_dec(v___x_2422_);
                        v___x_2504_ = crate::leanh::lean_box(0);
                        v_isShared_2505_ = v_isSharedCheck_2509_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2423_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_2415_);
                    v_val_2427_ = crate::leanh::lean_ctor_get(v_a_2423_, 0);
                    v_isSharedCheck_2439_ = (!crate::leanh::lean_is_exclusive(v_a_2423_)) as u8;
                    if v_isSharedCheck_2439_ == 0 {
                        v___x_2429_ = v_a_2423_;
                        v_isShared_2430_ = v_isSharedCheck_2439_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2427_);
                        crate::leanh::lean_dec(v_a_2423_);
                        v___x_2429_ = crate::leanh::lean_box(0);
                        v_isShared_2430_ = v_isSharedCheck_2439_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2425_);
                    crate::leanh::lean_dec(v_a_2423_);
                    v___x_2440_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2415_, v_a_2417_);
                    if crate::leanh::lean_obj_tag(v___x_2440_) == 0 {
                        v_a_2441_ = crate::leanh::lean_ctor_get(v___x_2440_, 0);
                        v_isSharedCheck_2492_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2440_)) as u8;
                        if v_isSharedCheck_2492_ == 0 {
                            v___x_2443_ = v___x_2440_;
                            v_isShared_2444_ = v_isSharedCheck_2492_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2441_);
                            crate::leanh::lean_dec(v___x_2440_);
                            v___x_2443_ = crate::leanh::lean_box(0);
                            v_isShared_2444_ = v_isSharedCheck_2492_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_2493_ = crate::leanh::lean_ctor_get(v___x_2440_, 0);
                        v_isSharedCheck_2500_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2440_)) as u8;
                        if v_isSharedCheck_2500_ == 0 {
                            v___x_2495_ = v___x_2440_;
                            v_isShared_2496_ = v_isSharedCheck_2500_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2493_);
                            crate::leanh::lean_dec(v___x_2440_);
                            v___x_2495_ = crate::leanh::lean_box(0);
                            v_isShared_2496_ = v_isSharedCheck_2500_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_fst_2431_ = crate::leanh::lean_ctor_get(v_val_2427_, 0);
                crate::leanh::lean_inc(v_fst_2431_);
                crate::leanh::lean_dec(v_val_2427_);
                v___x_2432_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_2431_);
                if v_isShared_2430_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2429_, 0, v___x_2432_);
                    v___x_2434_ = v___x_2429_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2438_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2432_);
                    v___x_2434_ = v_reuseFailAlloc_2438_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2434_);
                    v___x_2436_ = v___x_2425_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
                    v___x_2436_ = v_reuseFailAlloc_2437_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2436_;
            }
            5 => {
                v___x_2450_ = l_Lean_Expr_cleanupAnnotations(v_a_2441_);
                v___x_2451_ = l_Lean_Expr_isApp(v___x_2450_);
                if v___x_2451_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2450_);
                    state = 6;
                    continue;
                } else {
                    v_arg_2452_ = crate::leanh::lean_ctor_get(v___x_2450_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2452_);
                    v___x_2453_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2450_);
                    v___x_2454_ = l_Lean_Expr_isApp(v___x_2453_);
                    if v___x_2454_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2453_);
                        crate::leanh::lean_dec_ref(v_arg_2452_);
                        state = 6;
                        continue;
                    } else {
                        v___x_2455_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2453_);
                        v___x_2456_ = l_Lean_Expr_isApp(v___x_2455_);
                        if v___x_2456_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2455_);
                            crate::leanh::lean_dec_ref(v_arg_2452_);
                            state = 6;
                            continue;
                        } else {
                            v___x_2457_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2455_);
                            v___x_2458_ = l_Lean_Meta_getIntValue_x3f___closed__4;
                            v___x_2459_ = l_Lean_Expr_isConstOf(v___x_2457_, v___x_2458_);
                            crate::leanh::lean_dec_ref(v___x_2457_);
                            if v___x_2459_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2452_);
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_2443_);
                                v___x_2460_ = l_Lean_Meta_getOfNatValue_x3f(
                                    v_arg_2452_,
                                    v___x_2421_,
                                    v_a_2416_,
                                    v_a_2417_,
                                    v_a_2418_,
                                    v_a_2419_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2460_) == 0 {
                                    v_a_2461_ = crate::leanh::lean_ctor_get(v___x_2460_, 0);
                                    v_isSharedCheck_2483_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2460_)) as u8;
                                    if v_isSharedCheck_2483_ == 0 {
                                        v___x_2463_ = v___x_2460_;
                                        v_isShared_2464_ = v_isSharedCheck_2483_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2461_);
                                        crate::leanh::lean_dec(v___x_2460_);
                                        v___x_2463_ = crate::leanh::lean_box(0);
                                        v_isShared_2464_ = v_isSharedCheck_2483_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v_a_2484_ = crate::leanh::lean_ctor_get(v___x_2460_, 0);
                                    v_isSharedCheck_2491_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2460_)) as u8;
                                    if v_isSharedCheck_2491_ == 0 {
                                        v___x_2486_ = v___x_2460_;
                                        v_isShared_2487_ = v_isSharedCheck_2491_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2484_);
                                        crate::leanh::lean_dec(v___x_2460_);
                                        v___x_2486_ = crate::leanh::lean_box(0);
                                        v_isShared_2487_ = v_isSharedCheck_2491_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            6 => {
                v___x_2446_ = crate::leanh::lean_box(0);
                if v_isShared_2444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2443_, 0, v___x_2446_);
                    v___x_2448_ = v___x_2443_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
                    v___x_2448_ = v_reuseFailAlloc_2449_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2448_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_2461_) == 1 {
                    v_val_2465_ = crate::leanh::lean_ctor_get(v_a_2461_, 0);
                    v_isSharedCheck_2478_ = (!crate::leanh::lean_is_exclusive(v_a_2461_)) as u8;
                    if v_isSharedCheck_2478_ == 0 {
                        v___x_2467_ = v_a_2461_;
                        v_isShared_2468_ = v_isSharedCheck_2478_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2465_);
                        crate::leanh::lean_dec(v_a_2461_);
                        v___x_2467_ = crate::leanh::lean_box(0);
                        v_isShared_2468_ = v_isSharedCheck_2478_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2461_);
                    v___x_2479_ = crate::leanh::lean_box(0);
                    if v_isShared_2464_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2479_);
                        v___x_2481_ = v___x_2463_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
                        v___x_2481_ = v_reuseFailAlloc_2482_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                v_fst_2469_ = crate::leanh::lean_ctor_get(v_val_2465_, 0);
                crate::leanh::lean_inc(v_fst_2469_);
                crate::leanh::lean_dec(v_val_2465_);
                v___x_2470_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_2469_);
                v___x_2471_ = l_Rat_neg(v___x_2470_);
                if v_isShared_2468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2467_, 0, v___x_2471_);
                    v___x_2473_ = v___x_2467_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2471_);
                    v___x_2473_ = v_reuseFailAlloc_2477_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2464_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2463_, 0, v___x_2473_);
                    v___x_2475_ = v___x_2463_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2473_);
                    v___x_2475_ = v_reuseFailAlloc_2476_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2475_;
            }
            12 => {
                return v___x_2481_;
            }
            13 => {
                if v_isShared_2487_ == 0 {
                    v___x_2489_ = v___x_2486_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
                    v___x_2489_ = v_reuseFailAlloc_2490_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2489_;
            }
            15 => {
                if v_isShared_2496_ == 0 {
                    v___x_2498_ = v___x_2495_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_a_2493_);
                    v___x_2498_ = v_reuseFailAlloc_2499_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2498_;
            }
            17 => {
                if v_isShared_2505_ == 0 {
                    v___x_2507_ = v___x_2504_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
                    v___x_2507_ = v_reuseFailAlloc_2508_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___boxed(
    mut v_e_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
    mut v_a_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2516_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(
        v_e_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_,
    );
    crate::leanh::lean_dec(v_a_2514_);
    crate::leanh::lean_dec_ref(v_a_2513_);
    crate::leanh::lean_dec(v_a_2512_);
    crate::leanh::lean_dec_ref(v_a_2511_);
    return v_res_2516_;
}
pub unsafe fn l_Lean_Meta_getRatValue_x3f(
    mut v_e_2522_: *mut crate::leanh::LeanObject,
    mut v_a_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
    mut v_a_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v_val_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2565_: u8 = 0;
    let mut v_val_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v_fst_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut v_a_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2592_: u8 = 0;
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2597_: u8 = 0;
    let mut v_a_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2522_);
                v___x_2528_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2522_, v_a_2524_);
                if crate::leanh::lean_obj_tag(v___x_2528_) == 0 {
                    v_a_2529_ = crate::leanh::lean_ctor_get(v___x_2528_, 0);
                    crate::leanh::lean_inc(v_a_2529_);
                    crate::leanh::lean_dec_ref_known(v___x_2528_, 1);
                    v___x_2530_ = l_Lean_Expr_cleanupAnnotations(v_a_2529_);
                    v___x_2531_ = l_Lean_Expr_isApp(v___x_2530_);
                    if v___x_2531_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2530_);
                        v___x_2532_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                        return v___x_2532_;
                    } else {
                        v_arg_2533_ = crate::leanh::lean_ctor_get(v___x_2530_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2533_);
                        v___x_2534_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2530_);
                        v___x_2535_ = l_Lean_Expr_isApp(v___x_2534_);
                        if v___x_2535_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2534_);
                            crate::leanh::lean_dec_ref(v_arg_2533_);
                            v___x_2536_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                            return v___x_2536_;
                        } else {
                            v_arg_2537_ = crate::leanh::lean_ctor_get(v___x_2534_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2537_);
                            v___x_2538_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2534_);
                            v___x_2539_ = l_Lean_Expr_isApp(v___x_2538_);
                            if v___x_2539_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2538_);
                                crate::leanh::lean_dec_ref(v_arg_2537_);
                                crate::leanh::lean_dec_ref(v_arg_2533_);
                                v___x_2540_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                                return v___x_2540_;
                            } else {
                                v___x_2541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2538_);
                                v___x_2542_ = l_Lean_Expr_isApp(v___x_2541_);
                                if v___x_2542_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2541_);
                                    crate::leanh::lean_dec_ref(v_arg_2537_);
                                    crate::leanh::lean_dec_ref(v_arg_2533_);
                                    v___x_2543_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                                    return v___x_2543_;
                                } else {
                                    v___x_2544_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2541_);
                                    v___x_2545_ = l_Lean_Expr_isApp(v___x_2544_);
                                    if v___x_2545_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_2544_);
                                        crate::leanh::lean_dec_ref(v_arg_2537_);
                                        crate::leanh::lean_dec_ref(v_arg_2533_);
                                        v___x_2546_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                                        return v___x_2546_;
                                    } else {
                                        v___x_2547_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_2544_);
                                        v___x_2548_ = l_Lean_Expr_isApp(v___x_2547_);
                                        if v___x_2548_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_2547_);
                                            crate::leanh::lean_dec_ref(v_arg_2537_);
                                            crate::leanh::lean_dec_ref(v_arg_2533_);
                                            v___x_2549_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                                            return v___x_2549_;
                                        } else {
                                            v___x_2550_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2547_);
                                            v___x_2551_ = l_Lean_Meta_getRatValue_x3f___closed__2;
                                            v___x_2552_ =
                                                l_Lean_Expr_isConstOf(v___x_2550_, v___x_2551_);
                                            crate::leanh::lean_dec_ref(v___x_2550_);
                                            if v___x_2552_ == 0 {
                                                crate::leanh::lean_dec_ref(v_arg_2537_);
                                                crate::leanh::lean_dec_ref(v_arg_2533_);
                                                v___x_2553_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_e_2522_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                                                return v___x_2553_;
                                            } else {
                                                crate::leanh::lean_dec_ref(v_e_2522_);
                                                v___x_2554_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f(v_arg_2537_, v_a_2523_, v_a_2524_, v_a_2525_, v_a_2526_);
                                                if crate::leanh::lean_obj_tag(v___x_2554_) == 0 {
                                                    v_a_2555_ =
                                                        crate::leanh::lean_ctor_get(v___x_2554_, 0);
                                                    v_isSharedCheck_2597_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2554_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2597_ == 0 {
                                                        v___x_2557_ = v___x_2554_;
                                                        v_isShared_2558_ = v_isSharedCheck_2597_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_2555_);
                                                        crate::leanh::lean_dec(v___x_2554_);
                                                        v___x_2557_ = crate::leanh::lean_box(0);
                                                        v_isShared_2558_ = v_isSharedCheck_2597_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_arg_2533_);
                                                    return v___x_2554_;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2522_);
                    v_a_2598_ = crate::leanh::lean_ctor_get(v___x_2528_, 0);
                    v_isSharedCheck_2605_ = (!crate::leanh::lean_is_exclusive(v___x_2528_)) as u8;
                    if v_isSharedCheck_2605_ == 0 {
                        v___x_2600_ = v___x_2528_;
                        v_isShared_2601_ = v_isSharedCheck_2605_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2598_);
                        crate::leanh::lean_dec(v___x_2528_);
                        v___x_2600_ = crate::leanh::lean_box(0);
                        v_isShared_2601_ = v_isSharedCheck_2605_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2555_) == 1 {
                    crate::leanh::lean_del_object(v___x_2557_);
                    v_val_2559_ = crate::leanh::lean_ctor_get(v_a_2555_, 0);
                    crate::leanh::lean_inc(v_val_2559_);
                    crate::leanh::lean_dec_ref_known(v_a_2555_, 1);
                    v___x_2560_ = l___private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f___closed__1;
                    v___x_2561_ = l_Lean_Meta_getOfNatValue_x3f(
                        v_arg_2533_,
                        v___x_2560_,
                        v_a_2523_,
                        v_a_2524_,
                        v_a_2525_,
                        v_a_2526_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2561_) == 0 {
                        v_a_2562_ = crate::leanh::lean_ctor_get(v___x_2561_, 0);
                        v_isSharedCheck_2584_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2561_)) as u8;
                        if v_isSharedCheck_2584_ == 0 {
                            v___x_2564_ = v___x_2561_;
                            v_isShared_2565_ = v_isSharedCheck_2584_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2562_);
                            crate::leanh::lean_dec(v___x_2561_);
                            v___x_2564_ = crate::leanh::lean_box(0);
                            v_isShared_2565_ = v_isSharedCheck_2584_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2559_);
                        v_a_2585_ = crate::leanh::lean_ctor_get(v___x_2561_, 0);
                        v_isSharedCheck_2592_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2561_)) as u8;
                        if v_isSharedCheck_2592_ == 0 {
                            v___x_2587_ = v___x_2561_;
                            v_isShared_2588_ = v_isSharedCheck_2592_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2585_);
                            crate::leanh::lean_dec(v___x_2561_);
                            v___x_2587_ = crate::leanh::lean_box(0);
                            v_isShared_2588_ = v_isSharedCheck_2592_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2555_);
                    crate::leanh::lean_dec_ref(v_arg_2533_);
                    v___x_2593_ = crate::leanh::lean_box(0);
                    if v_isShared_2558_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2557_, 0, v___x_2593_);
                        v___x_2595_ = v___x_2557_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
                        v___x_2595_ = v_reuseFailAlloc_2596_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2562_) == 1 {
                    v_val_2566_ = crate::leanh::lean_ctor_get(v_a_2562_, 0);
                    v_isSharedCheck_2579_ = (!crate::leanh::lean_is_exclusive(v_a_2562_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v___x_2568_ = v_a_2562_;
                        v_isShared_2569_ = v_isSharedCheck_2579_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2566_);
                        crate::leanh::lean_dec(v_a_2562_);
                        v___x_2568_ = crate::leanh::lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2579_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2562_);
                    crate::leanh::lean_dec(v_val_2559_);
                    v___x_2580_ = crate::leanh::lean_box(0);
                    if v_isShared_2565_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2580_);
                        v___x_2582_ = v___x_2564_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
                        v___x_2582_ = v_reuseFailAlloc_2583_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_2570_ = crate::leanh::lean_ctor_get(v_val_2566_, 0);
                crate::leanh::lean_inc(v_fst_2570_);
                crate::leanh::lean_dec(v_val_2566_);
                v___x_2571_ = l_Nat_cast___at___00__private_Lean_Meta_LitValues_0__Lean_Meta_getRatValue_x3f_getRatValueNum_x3f_spec__0(v_fst_2570_);
                v___x_2572_ = l_Rat_div(v_val_2559_, v___x_2571_);
                crate::leanh::lean_dec(v_val_2559_);
                if v_isShared_2569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2572_);
                    v___x_2574_ = v___x_2568_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2572_);
                    v___x_2574_ = v_reuseFailAlloc_2578_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2565_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2564_, 0, v___x_2574_);
                    v___x_2576_ = v___x_2564_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2574_);
                    v___x_2576_ = v_reuseFailAlloc_2577_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2576_;
            }
            6 => {
                return v___x_2582_;
            }
            7 => {
                if v_isShared_2588_ == 0 {
                    v___x_2590_ = v___x_2587_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
                    v___x_2590_ = v_reuseFailAlloc_2591_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2590_;
            }
            9 => {
                return v___x_2595_;
            }
            10 => {
                if v_isShared_2601_ == 0 {
                    v___x_2603_ = v___x_2600_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
                    v___x_2603_ = v_reuseFailAlloc_2604_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getRatValue_x3f___boxed(
    mut v_e_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2612_ =
        l_Lean_Meta_getRatValue_x3f(v_e_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
    crate::leanh::lean_dec(v_a_2610_);
    crate::leanh::lean_dec_ref(v_a_2609_);
    crate::leanh::lean_dec(v_a_2608_);
    crate::leanh::lean_dec_ref(v_a_2607_);
    return v_res_2612_;
}
pub unsafe fn l_Lean_Meta_getCharValue_x3f(
    mut v_e_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
    mut v_a_2619_: *mut crate::leanh::LeanObject,
    mut v_a_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2627_: u8 = 0;
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: u8 = 0;
    let mut v_arg_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v_val_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v___x_2648_: u32 = 0;
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2656_: u8 = 0;
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut v_a_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut v_isSharedCheck_2670_: u8 = 0;
    let mut v_a_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2623_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2617_, v_a_2619_);
                if crate::leanh::lean_obj_tag(v___x_2623_) == 0 {
                    v_a_2624_ = crate::leanh::lean_ctor_get(v___x_2623_, 0);
                    v_isSharedCheck_2670_ = (!crate::leanh::lean_is_exclusive(v___x_2623_)) as u8;
                    if v_isSharedCheck_2670_ == 0 {
                        v___x_2626_ = v___x_2623_;
                        v_isShared_2627_ = v_isSharedCheck_2670_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2624_);
                        crate::leanh::lean_dec(v___x_2623_);
                        v___x_2626_ = crate::leanh::lean_box(0);
                        v_isShared_2627_ = v_isSharedCheck_2670_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2671_ = crate::leanh::lean_ctor_get(v___x_2623_, 0);
                    v_isSharedCheck_2678_ = (!crate::leanh::lean_is_exclusive(v___x_2623_)) as u8;
                    if v_isSharedCheck_2678_ == 0 {
                        v___x_2673_ = v___x_2623_;
                        v_isShared_2674_ = v_isSharedCheck_2678_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2671_);
                        crate::leanh::lean_dec(v___x_2623_);
                        v___x_2673_ = crate::leanh::lean_box(0);
                        v_isShared_2674_ = v_isSharedCheck_2678_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2633_ = l_Lean_Expr_cleanupAnnotations(v_a_2624_);
                v___x_2634_ = l_Lean_Expr_isApp(v___x_2633_);
                if v___x_2634_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2633_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2635_ = crate::leanh::lean_ctor_get(v___x_2633_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2635_);
                    v___x_2636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2633_);
                    v___x_2637_ = l_Lean_Meta_getCharValue_x3f___closed__1;
                    v___x_2638_ = l_Lean_Expr_isConstOf(v___x_2636_, v___x_2637_);
                    crate::leanh::lean_dec_ref(v___x_2636_);
                    if v___x_2638_ == 0 {
                        crate::leanh::lean_dec_ref(v_arg_2635_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2626_);
                        v___x_2639_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_2635_,
                            v_a_2618_,
                            v_a_2619_,
                            v_a_2620_,
                            v_a_2621_,
                        );
                        crate::leanh::lean_dec_ref(v_arg_2635_);
                        if crate::leanh::lean_obj_tag(v___x_2639_) == 0 {
                            v_a_2640_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                            v_isSharedCheck_2661_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2639_)) as u8;
                            if v_isSharedCheck_2661_ == 0 {
                                v___x_2642_ = v___x_2639_;
                                v_isShared_2643_ = v_isSharedCheck_2661_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2640_);
                                crate::leanh::lean_dec(v___x_2639_);
                                v___x_2642_ = crate::leanh::lean_box(0);
                                v_isShared_2643_ = v_isSharedCheck_2661_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v_a_2662_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                            v_isSharedCheck_2669_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2639_)) as u8;
                            if v_isSharedCheck_2669_ == 0 {
                                v___x_2664_ = v___x_2639_;
                                v_isShared_2665_ = v_isSharedCheck_2669_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2662_);
                                crate::leanh::lean_dec(v___x_2639_);
                                v___x_2664_ = crate::leanh::lean_box(0);
                                v_isShared_2665_ = v_isSharedCheck_2669_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2629_ = crate::leanh::lean_box(0);
                if v_isShared_2627_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2626_, 0, v___x_2629_);
                    v___x_2631_ = v___x_2626_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2629_);
                    v___x_2631_ = v_reuseFailAlloc_2632_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2631_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2640_) == 1 {
                    v_val_2644_ = crate::leanh::lean_ctor_get(v_a_2640_, 0);
                    v_isSharedCheck_2656_ = (!crate::leanh::lean_is_exclusive(v_a_2640_)) as u8;
                    if v_isSharedCheck_2656_ == 0 {
                        v___x_2646_ = v_a_2640_;
                        v_isShared_2647_ = v_isSharedCheck_2656_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2644_);
                        crate::leanh::lean_dec(v_a_2640_);
                        v___x_2646_ = crate::leanh::lean_box(0);
                        v_isShared_2647_ = v_isSharedCheck_2656_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2640_);
                    v___x_2657_ = crate::leanh::lean_box(0);
                    if v_isShared_2643_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2657_);
                        v___x_2659_ = v___x_2642_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
                        v___x_2659_ = v_reuseFailAlloc_2660_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_2648_ = l_Char_ofNat(v_val_2644_);
                crate::leanh::lean_dec(v_val_2644_);
                v___x_2649_ = crate::leanh::lean_box_uint32(v___x_2648_);
                if v_isShared_2647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2646_, 0, v___x_2649_);
                    v___x_2651_ = v___x_2646_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2649_);
                    v___x_2651_ = v_reuseFailAlloc_2655_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2651_);
                    v___x_2653_ = v___x_2642_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
                    v___x_2653_ = v_reuseFailAlloc_2654_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2653_;
            }
            8 => {
                return v___x_2659_;
            }
            9 => {
                if v_isShared_2665_ == 0 {
                    v___x_2667_ = v___x_2664_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
                    v___x_2667_ = v_reuseFailAlloc_2668_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2667_;
            }
            11 => {
                if v_isShared_2674_ == 0 {
                    v___x_2676_ = v___x_2673_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
                    v___x_2676_ = v_reuseFailAlloc_2677_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getCharValue_x3f___boxed(
    mut v_e_2679_: *mut crate::leanh::LeanObject,
    mut v_a_2680_: *mut crate::leanh::LeanObject,
    mut v_a_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
    mut v_a_2683_: *mut crate::leanh::LeanObject,
    mut v_a_2684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2685_ =
        l_Lean_Meta_getCharValue_x3f(v_e_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
    crate::leanh::lean_dec(v_a_2683_);
    crate::leanh::lean_dec_ref(v_a_2682_);
    crate::leanh::lean_dec(v_a_2681_);
    crate::leanh::lean_dec_ref(v_a_2680_);
    return v_res_2685_;
}
pub unsafe fn l_Lean_Meta_getStringValue_x3f(
    mut v_e_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2691_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2695_: u8 = 0;
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_2686_) == 9 {
                    v_a_2687_ = crate::leanh::lean_ctor_get(v_e_2686_, 0);
                    crate::leanh::lean_inc_ref(v_a_2687_);
                    crate::leanh::lean_dec_ref_known(v_e_2686_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2687_) == 1 {
                        v_val_2688_ = crate::leanh::lean_ctor_get(v_a_2687_, 0);
                        v_isSharedCheck_2695_ = (!crate::leanh::lean_is_exclusive(v_a_2687_)) as u8;
                        if v_isSharedCheck_2695_ == 0 {
                            v___x_2690_ = v_a_2687_;
                            v_isShared_2691_ = v_isSharedCheck_2695_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2688_);
                            crate::leanh::lean_dec(v_a_2687_);
                            v___x_2690_ = crate::leanh::lean_box(0);
                            v_isShared_2691_ = v_isSharedCheck_2695_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2687_);
                        v___x_2696_ = crate::leanh::lean_box(0);
                        return v___x_2696_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2686_);
                    v___x_2697_ = crate::leanh::lean_box(0);
                    return v___x_2697_;
                }
            }
            1 => {
                if v_isShared_2691_ == 0 {
                    v___x_2693_ = v___x_2690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_val_2688_);
                    v___x_2693_ = v_reuseFailAlloc_2694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getFinValue_x3f(
    mut v_e_2701_: *mut crate::leanh::LeanObject,
    mut v_a_2702_: *mut crate::leanh::LeanObject,
    mut v_a_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2712_: u8 = 0;
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2722_: u8 = 0;
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2730_: u8 = 0;
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2738_: u8 = 0;
    let mut v_zero_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2740_: u8 = 0;
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2758_: u8 = 0;
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v_a_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2763_: u8 = 0;
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2767_: u8 = 0;
    let mut v_a_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut v_isSharedCheck_2776_: u8 = 0;
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut v_a_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2781_: u8 = 0;
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2707_ = l_Lean_Meta_getFinValue_x3f___closed__1;
                v___x_2708_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_2701_,
                    v___x_2707_,
                    v_a_2702_,
                    v_a_2703_,
                    v_a_2704_,
                    v_a_2705_,
                );
                if crate::leanh::lean_obj_tag(v___x_2708_) == 0 {
                    v_a_2709_ = crate::leanh::lean_ctor_get(v___x_2708_, 0);
                    v_isSharedCheck_2777_ = (!crate::leanh::lean_is_exclusive(v___x_2708_)) as u8;
                    if v_isSharedCheck_2777_ == 0 {
                        v___x_2711_ = v___x_2708_;
                        v_isShared_2712_ = v_isSharedCheck_2777_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2709_);
                        crate::leanh::lean_dec(v___x_2708_);
                        v___x_2711_ = crate::leanh::lean_box(0);
                        v_isShared_2712_ = v_isSharedCheck_2777_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2778_ = crate::leanh::lean_ctor_get(v___x_2708_, 0);
                    v_isSharedCheck_2785_ = (!crate::leanh::lean_is_exclusive(v___x_2708_)) as u8;
                    if v_isSharedCheck_2785_ == 0 {
                        v___x_2780_ = v___x_2708_;
                        v_isShared_2781_ = v_isSharedCheck_2785_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2778_);
                        crate::leanh::lean_dec(v___x_2708_);
                        v___x_2780_ = crate::leanh::lean_box(0);
                        v_isShared_2781_ = v_isSharedCheck_2785_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2709_) == 0 {
                    v___x_2713_ = crate::leanh::lean_box(0);
                    if v_isShared_2712_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2711_, 0, v___x_2713_);
                        v___x_2715_ = v___x_2711_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2713_);
                        v___x_2715_ = v_reuseFailAlloc_2716_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2711_);
                    v_val_2717_ = crate::leanh::lean_ctor_get(v_a_2709_, 0);
                    crate::leanh::lean_inc(v_val_2717_);
                    crate::leanh::lean_dec_ref_known(v_a_2709_, 1);
                    v_fst_2718_ = crate::leanh::lean_ctor_get(v_val_2717_, 0);
                    v_snd_2719_ = crate::leanh::lean_ctor_get(v_val_2717_, 1);
                    v_isSharedCheck_2776_ = (!crate::leanh::lean_is_exclusive(v_val_2717_)) as u8;
                    if v_isSharedCheck_2776_ == 0 {
                        v___x_2721_ = v_val_2717_;
                        v_isShared_2722_ = v_isSharedCheck_2776_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2719_);
                        crate::leanh::lean_inc(v_fst_2718_);
                        crate::leanh::lean_dec(v_val_2717_);
                        v___x_2721_ = crate::leanh::lean_box(0);
                        v_isShared_2722_ = v_isSharedCheck_2776_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2715_;
            }
            3 => {
                v___x_2723_ = l_Lean_Expr_appArg_x21(v_snd_2719_);
                crate::leanh::lean_dec(v_snd_2719_);
                v___x_2724_ =
                    l_Lean_Meta_whnfD(v___x_2723_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
                if crate::leanh::lean_obj_tag(v___x_2724_) == 0 {
                    v_a_2725_ = crate::leanh::lean_ctor_get(v___x_2724_, 0);
                    crate::leanh::lean_inc(v_a_2725_);
                    crate::leanh::lean_dec_ref_known(v___x_2724_, 1);
                    v___x_2726_ = l_Lean_Meta_getNatValue_x3f(
                        v_a_2725_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_,
                    );
                    crate::leanh::lean_dec(v_a_2725_);
                    if crate::leanh::lean_obj_tag(v___x_2726_) == 0 {
                        v_a_2727_ = crate::leanh::lean_ctor_get(v___x_2726_, 0);
                        v_isSharedCheck_2759_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2726_)) as u8;
                        if v_isSharedCheck_2759_ == 0 {
                            v___x_2729_ = v___x_2726_;
                            v_isShared_2730_ = v_isSharedCheck_2759_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2727_);
                            crate::leanh::lean_dec(v___x_2726_);
                            v___x_2729_ = crate::leanh::lean_box(0);
                            v_isShared_2730_ = v_isSharedCheck_2759_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2721_);
                        crate::leanh::lean_dec(v_fst_2718_);
                        v_a_2760_ = crate::leanh::lean_ctor_get(v___x_2726_, 0);
                        v_isSharedCheck_2767_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2726_)) as u8;
                        if v_isSharedCheck_2767_ == 0 {
                            v___x_2762_ = v___x_2726_;
                            v_isShared_2763_ = v_isSharedCheck_2767_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2760_);
                            crate::leanh::lean_dec(v___x_2726_);
                            v___x_2762_ = crate::leanh::lean_box(0);
                            v_isShared_2763_ = v_isSharedCheck_2767_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2721_);
                    crate::leanh::lean_dec(v_fst_2718_);
                    v_a_2768_ = crate::leanh::lean_ctor_get(v___x_2724_, 0);
                    v_isSharedCheck_2775_ = (!crate::leanh::lean_is_exclusive(v___x_2724_)) as u8;
                    if v_isSharedCheck_2775_ == 0 {
                        v___x_2770_ = v___x_2724_;
                        v_isShared_2771_ = v_isSharedCheck_2775_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2768_);
                        crate::leanh::lean_dec(v___x_2724_);
                        v___x_2770_ = crate::leanh::lean_box(0);
                        v_isShared_2771_ = v_isSharedCheck_2775_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2727_) == 0 {
                    crate::leanh::lean_del_object(v___x_2721_);
                    crate::leanh::lean_dec(v_fst_2718_);
                    v___x_2731_ = crate::leanh::lean_box(0);
                    if v_isShared_2730_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2729_, 0, v___x_2731_);
                        v___x_2733_ = v___x_2729_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2734_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2734_, 0, v___x_2731_);
                        v___x_2733_ = v_reuseFailAlloc_2734_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_2735_ = crate::leanh::lean_ctor_get(v_a_2727_, 0);
                    v_isSharedCheck_2758_ = (!crate::leanh::lean_is_exclusive(v_a_2727_)) as u8;
                    if v_isSharedCheck_2758_ == 0 {
                        v___x_2737_ = v_a_2727_;
                        v_isShared_2738_ = v_isSharedCheck_2758_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2735_);
                        crate::leanh::lean_dec(v_a_2727_);
                        v___x_2737_ = crate::leanh::lean_box(0);
                        v_isShared_2738_ = v_isSharedCheck_2758_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2733_;
            }
            6 => {
                v_zero_2739_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2740_ = lean_nat_dec_eq(v_val_2735_, v_zero_2739_);
                if v_isZero_2740_ == 1 {
                    crate::leanh::lean_del_object(v___x_2737_);
                    crate::leanh::lean_dec(v_val_2735_);
                    crate::leanh::lean_del_object(v___x_2721_);
                    crate::leanh::lean_dec(v_fst_2718_);
                    v___x_2741_ = crate::leanh::lean_box(0);
                    if v_isShared_2730_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2729_, 0, v___x_2741_);
                        v___x_2743_ = v___x_2729_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2744_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
                        v___x_2743_ = v_reuseFailAlloc_2744_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_one_2745_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2746_ = lean_nat_sub(v_val_2735_, v_one_2745_);
                    crate::leanh::lean_dec(v_val_2735_);
                    v___x_2747_ = lean_nat_add(v_n_2746_, v_one_2745_);
                    crate::leanh::lean_dec(v_n_2746_);
                    v___x_2748_ = lean_nat_mod(v_fst_2718_, v___x_2747_);
                    crate::leanh::lean_dec(v_fst_2718_);
                    if v_isShared_2722_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2721_, 1, v___x_2748_);
                        crate::leanh::lean_ctor_set(v___x_2721_, 0, v___x_2747_);
                        v___x_2750_ = v___x_2721_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2757_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2747_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2748_);
                        v___x_2750_ = v_reuseFailAlloc_2757_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2743_;
            }
            8 => {
                if v_isShared_2738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2737_, 0, v___x_2750_);
                    v___x_2752_ = v___x_2737_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2750_);
                    v___x_2752_ = v_reuseFailAlloc_2756_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2729_, 0, v___x_2752_);
                    v___x_2754_ = v___x_2729_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2755_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
                    v___x_2754_ = v_reuseFailAlloc_2755_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2754_;
            }
            11 => {
                if v_isShared_2763_ == 0 {
                    v___x_2765_ = v___x_2762_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
                    v___x_2765_ = v_reuseFailAlloc_2766_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2765_;
            }
            13 => {
                if v_isShared_2771_ == 0 {
                    v___x_2773_ = v___x_2770_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
                    v___x_2773_ = v_reuseFailAlloc_2774_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2773_;
            }
            15 => {
                if v_isShared_2781_ == 0 {
                    v___x_2783_ = v___x_2780_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2784_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
                    v___x_2783_ = v_reuseFailAlloc_2784_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getFinValue_x3f___boxed(
    mut v_e_2786_: *mut crate::leanh::LeanObject,
    mut v_a_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_a_2789_: *mut crate::leanh::LeanObject,
    mut v_a_2790_: *mut crate::leanh::LeanObject,
    mut v_a_2791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2792_ =
        l_Lean_Meta_getFinValue_x3f(v_e_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_);
    crate::leanh::lean_dec(v_a_2790_);
    crate::leanh::lean_dec_ref(v_a_2789_);
    crate::leanh::lean_dec(v_a_2788_);
    crate::leanh::lean_dec_ref(v_a_2787_);
    return v_res_2792_;
}
pub unsafe fn l_Lean_Meta_getBitVecValue_x3f(
    mut v_e_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
    mut v_a_2805_: *mut crate::leanh::LeanObject,
    mut v_a_2806_: *mut crate::leanh::LeanObject,
    mut v_a_2807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nExpr_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vExpr_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2830_: u8 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2838_: u8 = 0;
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2847_: u8 = 0;
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_a_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2852_: u8 = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v_a_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2861_: u8 = 0;
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2865_: u8 = 0;
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2878_: u8 = 0;
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2888_: u8 = 0;
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2915_: u8 = 0;
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2924_: u8 = 0;
    let mut v_a_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_a_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u8 = 0;
    let mut v_arg_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: u8 = 0;
    let mut v_arg_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: u8 = 0;
    let mut v___x_2952_: u8 = 0;
    let mut v_arg_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v_a_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2803_);
                v___x_2866_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2803_, v_a_2805_);
                if crate::leanh::lean_obj_tag(v___x_2866_) == 0 {
                    v_a_2867_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                    crate::leanh::lean_inc(v_a_2867_);
                    crate::leanh::lean_dec_ref_known(v___x_2866_, 1);
                    v___x_2943_ = l_Lean_Expr_cleanupAnnotations(v_a_2867_);
                    v___x_2944_ = l_Lean_Expr_isApp(v___x_2943_);
                    if v___x_2944_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2943_);
                        v___y_2869_ = v_a_2804_;
                        v___y_2870_ = v_a_2805_;
                        v___y_2871_ = v_a_2806_;
                        v___y_2872_ = v_a_2807_;
                        state = 13;
                        continue;
                    } else {
                        v_arg_2945_ = crate::leanh::lean_ctor_get(v___x_2943_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2945_);
                        v___x_2946_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2943_);
                        v___x_2947_ = l_Lean_Expr_isApp(v___x_2946_);
                        if v___x_2947_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2946_);
                            crate::leanh::lean_dec_ref(v_arg_2945_);
                            v___y_2869_ = v_a_2804_;
                            v___y_2870_ = v_a_2805_;
                            v___y_2871_ = v_a_2806_;
                            v___y_2872_ = v_a_2807_;
                            state = 13;
                            continue;
                        } else {
                            v_arg_2948_ = crate::leanh::lean_ctor_get(v___x_2946_, 1);
                            crate::leanh::lean_inc_ref(v_arg_2948_);
                            v___x_2949_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2946_);
                            v___x_2950_ = l_Lean_Meta_getBitVecValue_x3f___closed__2;
                            v___x_2951_ = l_Lean_Expr_isConstOf(v___x_2949_, v___x_2950_);
                            if v___x_2951_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_2945_);
                                v___x_2952_ = l_Lean_Expr_isApp(v___x_2949_);
                                if v___x_2952_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_2949_);
                                    crate::leanh::lean_dec_ref(v_arg_2948_);
                                    v___y_2869_ = v_a_2804_;
                                    v___y_2870_ = v_a_2805_;
                                    v___y_2871_ = v_a_2806_;
                                    v___y_2872_ = v_a_2807_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_arg_2953_ = crate::leanh::lean_ctor_get(v___x_2949_, 1);
                                    crate::leanh::lean_inc_ref(v_arg_2953_);
                                    v___x_2954_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2949_);
                                    v___x_2955_ = l_Lean_Meta_getBitVecValue_x3f___closed__4;
                                    v___x_2956_ = l_Lean_Expr_isConstOf(v___x_2954_, v___x_2955_);
                                    crate::leanh::lean_dec_ref(v___x_2954_);
                                    if v___x_2956_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_2953_);
                                        crate::leanh::lean_dec_ref(v_arg_2948_);
                                        v___y_2869_ = v_a_2804_;
                                        v___y_2870_ = v_a_2805_;
                                        v___y_2871_ = v_a_2806_;
                                        v___y_2872_ = v_a_2807_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v_e_2803_);
                                        v_nExpr_2810_ = v_arg_2953_;
                                        v_vExpr_2811_ = v_arg_2948_;
                                        v___y_2812_ = v_a_2804_;
                                        v___y_2813_ = v_a_2805_;
                                        v___y_2814_ = v_a_2806_;
                                        v___y_2815_ = v_a_2807_;
                                        state = 1;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2949_);
                                crate::leanh::lean_dec_ref(v_e_2803_);
                                v_nExpr_2810_ = v_arg_2948_;
                                v_vExpr_2811_ = v_arg_2945_;
                                v___y_2812_ = v_a_2804_;
                                v___y_2813_ = v_a_2805_;
                                v___y_2814_ = v_a_2806_;
                                v___y_2815_ = v_a_2807_;
                                state = 1;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2803_);
                    v_a_2957_ = crate::leanh::lean_ctor_get(v___x_2866_, 0);
                    v_isSharedCheck_2964_ = (!crate::leanh::lean_is_exclusive(v___x_2866_)) as u8;
                    if v_isSharedCheck_2964_ == 0 {
                        v___x_2959_ = v___x_2866_;
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2957_);
                        crate::leanh::lean_dec(v___x_2866_);
                        v___x_2959_ = crate::leanh::lean_box(0);
                        v_isShared_2960_ = v_isSharedCheck_2964_;
                        state = 29;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2816_ = l_Lean_Meta_getNatValue_x3f(
                    v_nExpr_2810_,
                    v___y_2812_,
                    v___y_2813_,
                    v___y_2814_,
                    v___y_2815_,
                );
                crate::leanh::lean_dec_ref(v_nExpr_2810_);
                if crate::leanh::lean_obj_tag(v___x_2816_) == 0 {
                    v_a_2817_ = crate::leanh::lean_ctor_get(v___x_2816_, 0);
                    v_isSharedCheck_2857_ = (!crate::leanh::lean_is_exclusive(v___x_2816_)) as u8;
                    if v_isSharedCheck_2857_ == 0 {
                        v___x_2819_ = v___x_2816_;
                        v_isShared_2820_ = v_isSharedCheck_2857_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2817_);
                        crate::leanh::lean_dec(v___x_2816_);
                        v___x_2819_ = crate::leanh::lean_box(0);
                        v_isShared_2820_ = v_isSharedCheck_2857_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_vExpr_2811_);
                    v_a_2858_ = crate::leanh::lean_ctor_get(v___x_2816_, 0);
                    v_isSharedCheck_2865_ = (!crate::leanh::lean_is_exclusive(v___x_2816_)) as u8;
                    if v_isSharedCheck_2865_ == 0 {
                        v___x_2860_ = v___x_2816_;
                        v_isShared_2861_ = v_isSharedCheck_2865_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2858_);
                        crate::leanh::lean_dec(v___x_2816_);
                        v___x_2860_ = crate::leanh::lean_box(0);
                        v_isShared_2861_ = v_isSharedCheck_2865_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2817_) == 0 {
                    crate::leanh::lean_dec_ref(v_vExpr_2811_);
                    v___x_2821_ = crate::leanh::lean_box(0);
                    if v_isShared_2820_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2819_, 0, v___x_2821_);
                        v___x_2823_ = v___x_2819_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2824_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
                        v___x_2823_ = v_reuseFailAlloc_2824_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2819_);
                    v_val_2825_ = crate::leanh::lean_ctor_get(v_a_2817_, 0);
                    crate::leanh::lean_inc(v_val_2825_);
                    crate::leanh::lean_dec_ref_known(v_a_2817_, 1);
                    v___x_2826_ = l_Lean_Meta_getNatValue_x3f(
                        v_vExpr_2811_,
                        v___y_2812_,
                        v___y_2813_,
                        v___y_2814_,
                        v___y_2815_,
                    );
                    crate::leanh::lean_dec_ref(v_vExpr_2811_);
                    if crate::leanh::lean_obj_tag(v___x_2826_) == 0 {
                        v_a_2827_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                        v_isSharedCheck_2848_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2826_)) as u8;
                        if v_isSharedCheck_2848_ == 0 {
                            v___x_2829_ = v___x_2826_;
                            v_isShared_2830_ = v_isSharedCheck_2848_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2827_);
                            crate::leanh::lean_dec(v___x_2826_);
                            v___x_2829_ = crate::leanh::lean_box(0);
                            v_isShared_2830_ = v_isSharedCheck_2848_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2825_);
                        v_a_2849_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                        v_isSharedCheck_2856_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2826_)) as u8;
                        if v_isSharedCheck_2856_ == 0 {
                            v___x_2851_ = v___x_2826_;
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2849_);
                            crate::leanh::lean_dec(v___x_2826_);
                            v___x_2851_ = crate::leanh::lean_box(0);
                            v_isShared_2852_ = v_isSharedCheck_2856_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_2823_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_2827_) == 0 {
                    crate::leanh::lean_dec(v_val_2825_);
                    v___x_2831_ = crate::leanh::lean_box(0);
                    if v_isShared_2830_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2829_, 0, v___x_2831_);
                        v___x_2833_ = v___x_2829_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
                        v___x_2833_ = v_reuseFailAlloc_2834_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_2835_ = crate::leanh::lean_ctor_get(v_a_2827_, 0);
                    v_isSharedCheck_2847_ = (!crate::leanh::lean_is_exclusive(v_a_2827_)) as u8;
                    if v_isSharedCheck_2847_ == 0 {
                        v___x_2837_ = v_a_2827_;
                        v_isShared_2838_ = v_isSharedCheck_2847_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2835_);
                        crate::leanh::lean_dec(v_a_2827_);
                        v___x_2837_ = crate::leanh::lean_box(0);
                        v_isShared_2838_ = v_isSharedCheck_2847_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_2833_;
            }
            6 => {
                v___x_2839_ = l_BitVec_ofNat(v_val_2825_, v_val_2835_);
                crate::leanh::lean_dec(v_val_2835_);
                v___x_2840_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2840_, 0, v_val_2825_);
                crate::leanh::lean_ctor_set(v___x_2840_, 1, v___x_2839_);
                if v_isShared_2838_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2837_, 0, v___x_2840_);
                    v___x_2842_ = v___x_2837_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2840_);
                    v___x_2842_ = v_reuseFailAlloc_2846_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2829_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2829_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2844_;
            }
            9 => {
                if v_isShared_2852_ == 0 {
                    v___x_2854_ = v___x_2851_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
                    v___x_2854_ = v_reuseFailAlloc_2855_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2854_;
            }
            11 => {
                if v_isShared_2861_ == 0 {
                    v___x_2863_ = v___x_2860_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
                    v___x_2863_ = v_reuseFailAlloc_2864_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2863_;
            }
            13 => {
                v___x_2873_ = l_Lean_Meta_getBitVecValue_x3f___closed__1;
                v___x_2874_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_2803_,
                    v___x_2873_,
                    v___y_2869_,
                    v___y_2870_,
                    v___y_2871_,
                    v___y_2872_,
                );
                if crate::leanh::lean_obj_tag(v___x_2874_) == 0 {
                    v_a_2875_ = crate::leanh::lean_ctor_get(v___x_2874_, 0);
                    v_isSharedCheck_2934_ = (!crate::leanh::lean_is_exclusive(v___x_2874_)) as u8;
                    if v_isSharedCheck_2934_ == 0 {
                        v___x_2877_ = v___x_2874_;
                        v_isShared_2878_ = v_isSharedCheck_2934_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2875_);
                        crate::leanh::lean_dec(v___x_2874_);
                        v___x_2877_ = crate::leanh::lean_box(0);
                        v_isShared_2878_ = v_isSharedCheck_2934_;
                        state = 14;
                        continue;
                    }
                } else {
                    v_a_2935_ = crate::leanh::lean_ctor_get(v___x_2874_, 0);
                    v_isSharedCheck_2942_ = (!crate::leanh::lean_is_exclusive(v___x_2874_)) as u8;
                    if v_isSharedCheck_2942_ == 0 {
                        v___x_2937_ = v___x_2874_;
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2935_);
                        crate::leanh::lean_dec(v___x_2874_);
                        v___x_2937_ = crate::leanh::lean_box(0);
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 27;
                        continue;
                    }
                }
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_a_2875_) == 0 {
                    v___x_2879_ = crate::leanh::lean_box(0);
                    if v_isShared_2878_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2877_, 0, v___x_2879_);
                        v___x_2881_ = v___x_2877_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_2882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
                        v___x_2881_ = v_reuseFailAlloc_2882_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2877_);
                    v_val_2883_ = crate::leanh::lean_ctor_get(v_a_2875_, 0);
                    crate::leanh::lean_inc(v_val_2883_);
                    crate::leanh::lean_dec_ref_known(v_a_2875_, 1);
                    v_fst_2884_ = crate::leanh::lean_ctor_get(v_val_2883_, 0);
                    v_snd_2885_ = crate::leanh::lean_ctor_get(v_val_2883_, 1);
                    v_isSharedCheck_2933_ = (!crate::leanh::lean_is_exclusive(v_val_2883_)) as u8;
                    if v_isSharedCheck_2933_ == 0 {
                        v___x_2887_ = v_val_2883_;
                        v_isShared_2888_ = v_isSharedCheck_2933_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2885_);
                        crate::leanh::lean_inc(v_fst_2884_);
                        crate::leanh::lean_dec(v_val_2883_);
                        v___x_2887_ = crate::leanh::lean_box(0);
                        v_isShared_2888_ = v_isSharedCheck_2933_;
                        state = 16;
                        continue;
                    }
                }
            }
            15 => {
                return v___x_2881_;
            }
            16 => {
                v___x_2889_ = l_Lean_Expr_appArg_x21(v_snd_2885_);
                crate::leanh::lean_dec(v_snd_2885_);
                v___x_2890_ = l_Lean_Meta_whnfD(
                    v___x_2889_,
                    v___y_2869_,
                    v___y_2870_,
                    v___y_2871_,
                    v___y_2872_,
                );
                if crate::leanh::lean_obj_tag(v___x_2890_) == 0 {
                    v_a_2891_ = crate::leanh::lean_ctor_get(v___x_2890_, 0);
                    crate::leanh::lean_inc(v_a_2891_);
                    crate::leanh::lean_dec_ref_known(v___x_2890_, 1);
                    v___x_2892_ = l_Lean_Meta_getNatValue_x3f(
                        v_a_2891_,
                        v___y_2869_,
                        v___y_2870_,
                        v___y_2871_,
                        v___y_2872_,
                    );
                    crate::leanh::lean_dec(v_a_2891_);
                    if crate::leanh::lean_obj_tag(v___x_2892_) == 0 {
                        v_a_2893_ = crate::leanh::lean_ctor_get(v___x_2892_, 0);
                        v_isSharedCheck_2916_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2892_)) as u8;
                        if v_isSharedCheck_2916_ == 0 {
                            v___x_2895_ = v___x_2892_;
                            v_isShared_2896_ = v_isSharedCheck_2916_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2893_);
                            crate::leanh::lean_dec(v___x_2892_);
                            v___x_2895_ = crate::leanh::lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_2916_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2887_);
                        crate::leanh::lean_dec(v_fst_2884_);
                        v_a_2917_ = crate::leanh::lean_ctor_get(v___x_2892_, 0);
                        v_isSharedCheck_2924_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2892_)) as u8;
                        if v_isSharedCheck_2924_ == 0 {
                            v___x_2919_ = v___x_2892_;
                            v_isShared_2920_ = v_isSharedCheck_2924_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2917_);
                            crate::leanh::lean_dec(v___x_2892_);
                            v___x_2919_ = crate::leanh::lean_box(0);
                            v_isShared_2920_ = v_isSharedCheck_2924_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2887_);
                    crate::leanh::lean_dec(v_fst_2884_);
                    v_a_2925_ = crate::leanh::lean_ctor_get(v___x_2890_, 0);
                    v_isSharedCheck_2932_ = (!crate::leanh::lean_is_exclusive(v___x_2890_)) as u8;
                    if v_isSharedCheck_2932_ == 0 {
                        v___x_2927_ = v___x_2890_;
                        v_isShared_2928_ = v_isSharedCheck_2932_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2925_);
                        crate::leanh::lean_dec(v___x_2890_);
                        v___x_2927_ = crate::leanh::lean_box(0);
                        v_isShared_2928_ = v_isSharedCheck_2932_;
                        state = 25;
                        continue;
                    }
                }
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_a_2893_) == 0 {
                    crate::leanh::lean_del_object(v___x_2887_);
                    crate::leanh::lean_dec(v_fst_2884_);
                    v___x_2897_ = crate::leanh::lean_box(0);
                    if v_isShared_2896_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2895_, 0, v___x_2897_);
                        v___x_2899_ = v___x_2895_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_2900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2897_);
                        v___x_2899_ = v_reuseFailAlloc_2900_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_val_2901_ = crate::leanh::lean_ctor_get(v_a_2893_, 0);
                    v_isSharedCheck_2915_ = (!crate::leanh::lean_is_exclusive(v_a_2893_)) as u8;
                    if v_isSharedCheck_2915_ == 0 {
                        v___x_2903_ = v_a_2893_;
                        v_isShared_2904_ = v_isSharedCheck_2915_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2901_);
                        crate::leanh::lean_dec(v_a_2893_);
                        v___x_2903_ = crate::leanh::lean_box(0);
                        v_isShared_2904_ = v_isSharedCheck_2915_;
                        state = 19;
                        continue;
                    }
                }
            }
            18 => {
                return v___x_2899_;
            }
            19 => {
                v___x_2905_ = l_BitVec_ofNat(v_val_2901_, v_fst_2884_);
                crate::leanh::lean_dec(v_fst_2884_);
                if v_isShared_2888_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2887_, 1, v___x_2905_);
                    crate::leanh::lean_ctor_set(v___x_2887_, 0, v_val_2901_);
                    v___x_2907_ = v___x_2887_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2914_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_val_2901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 1, v___x_2905_);
                    v___x_2907_ = v_reuseFailAlloc_2914_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2907_);
                    v___x_2909_ = v___x_2903_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2907_);
                    v___x_2909_ = v_reuseFailAlloc_2913_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_2896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2895_, 0, v___x_2909_);
                    v___x_2911_ = v___x_2895_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
                    v___x_2911_ = v_reuseFailAlloc_2912_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2911_;
            }
            23 => {
                if v_isShared_2920_ == 0 {
                    v___x_2922_ = v___x_2919_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
                    v___x_2922_ = v_reuseFailAlloc_2923_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2922_;
            }
            25 => {
                if v_isShared_2928_ == 0 {
                    v___x_2930_ = v___x_2927_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
                    v___x_2930_ = v_reuseFailAlloc_2931_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_2930_;
            }
            27 => {
                if v_isShared_2938_ == 0 {
                    v___x_2940_ = v___x_2937_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
                    v___x_2940_ = v_reuseFailAlloc_2941_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2940_;
            }
            29 => {
                if v_isShared_2960_ == 0 {
                    v___x_2962_ = v___x_2959_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2963_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
                    v___x_2962_ = v_reuseFailAlloc_2963_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getBitVecValue_x3f___boxed(
    mut v_e_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ =
        l_Lean_Meta_getBitVecValue_x3f(v_e_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_);
    crate::leanh::lean_dec(v_a_2969_);
    crate::leanh::lean_dec_ref(v_a_2968_);
    crate::leanh::lean_dec(v_a_2967_);
    crate::leanh::lean_dec_ref(v_a_2966_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_Meta_getUInt8Value_x3f(
    mut v_e_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
    mut v_a_2977_: *mut crate::leanh::LeanObject,
    mut v_a_2978_: *mut crate::leanh::LeanObject,
    mut v_a_2979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2994_: u8 = 0;
    let mut v_fst_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3004_: u8 = 0;
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_a_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2981_ = l_Lean_Meta_getUInt8Value_x3f___closed__1;
                v___x_2982_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_2975_,
                    v___x_2981_,
                    v_a_2976_,
                    v_a_2977_,
                    v_a_2978_,
                    v_a_2979_,
                );
                if crate::leanh::lean_obj_tag(v___x_2982_) == 0 {
                    v_a_2983_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                    v_isSharedCheck_3005_ = (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                    if v_isSharedCheck_3005_ == 0 {
                        v___x_2985_ = v___x_2982_;
                        v_isShared_2986_ = v_isSharedCheck_3005_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2983_);
                        crate::leanh::lean_dec(v___x_2982_);
                        v___x_2985_ = crate::leanh::lean_box(0);
                        v_isShared_2986_ = v_isSharedCheck_3005_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3006_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                    v_isSharedCheck_3013_ = (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                    if v_isSharedCheck_3013_ == 0 {
                        v___x_3008_ = v___x_2982_;
                        v_isShared_3009_ = v_isSharedCheck_3013_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3006_);
                        crate::leanh::lean_dec(v___x_2982_);
                        v___x_3008_ = crate::leanh::lean_box(0);
                        v_isShared_3009_ = v_isSharedCheck_3013_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2983_) == 0 {
                    v___x_2987_ = crate::leanh::lean_box(0);
                    if v_isShared_2986_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2985_, 0, v___x_2987_);
                        v___x_2989_ = v___x_2985_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
                        v___x_2989_ = v_reuseFailAlloc_2990_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_2991_ = crate::leanh::lean_ctor_get(v_a_2983_, 0);
                    v_isSharedCheck_3004_ = (!crate::leanh::lean_is_exclusive(v_a_2983_)) as u8;
                    if v_isSharedCheck_3004_ == 0 {
                        v___x_2993_ = v_a_2983_;
                        v_isShared_2994_ = v_isSharedCheck_3004_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2991_);
                        crate::leanh::lean_dec(v_a_2983_);
                        v___x_2993_ = crate::leanh::lean_box(0);
                        v_isShared_2994_ = v_isSharedCheck_3004_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2989_;
            }
            3 => {
                v_fst_2995_ = crate::leanh::lean_ctor_get(v_val_2991_, 0);
                crate::leanh::lean_inc(v_fst_2995_);
                crate::leanh::lean_dec(v_val_2991_);
                v___x_2996_ = lean_uint8_of_nat(v_fst_2995_);
                crate::leanh::lean_dec(v_fst_2995_);
                v___x_2997_ = crate::leanh::lean_box((v___x_2996_) as usize);
                if v_isShared_2994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2993_, 0, v___x_2997_);
                    v___x_2999_ = v___x_2993_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3003_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_2997_);
                    v___x_2999_ = v_reuseFailAlloc_3003_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2986_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2985_, 0, v___x_2999_);
                    v___x_3001_ = v___x_2985_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v___x_2999_);
                    v___x_3001_ = v_reuseFailAlloc_3002_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3001_;
            }
            6 => {
                if v_isShared_3009_ == 0 {
                    v___x_3011_ = v___x_3008_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3011_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUInt8Value_x3f___boxed(
    mut v_e_3014_: *mut crate::leanh::LeanObject,
    mut v_a_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
    mut v_a_3017_: *mut crate::leanh::LeanObject,
    mut v_a_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3020_ =
        l_Lean_Meta_getUInt8Value_x3f(v_e_3014_, v_a_3015_, v_a_3016_, v_a_3017_, v_a_3018_);
    crate::leanh::lean_dec(v_a_3018_);
    crate::leanh::lean_dec_ref(v_a_3017_);
    crate::leanh::lean_dec(v_a_3016_);
    crate::leanh::lean_dec_ref(v_a_3015_);
    return v_res_3020_;
}
pub unsafe fn l_Lean_Meta_getUInt16Value_x3f(
    mut v_e_3024_: *mut crate::leanh::LeanObject,
    mut v_a_3025_: *mut crate::leanh::LeanObject,
    mut v_a_3026_: *mut crate::leanh::LeanObject,
    mut v_a_3027_: *mut crate::leanh::LeanObject,
    mut v_a_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3035_: u8 = 0;
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v_fst_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u16 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3053_: u8 = 0;
    let mut v_isSharedCheck_3054_: u8 = 0;
    let mut v_a_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3030_ = l_Lean_Meta_getUInt16Value_x3f___closed__1;
                v___x_3031_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_3024_,
                    v___x_3030_,
                    v_a_3025_,
                    v_a_3026_,
                    v_a_3027_,
                    v_a_3028_,
                );
                if crate::leanh::lean_obj_tag(v___x_3031_) == 0 {
                    v_a_3032_ = crate::leanh::lean_ctor_get(v___x_3031_, 0);
                    v_isSharedCheck_3054_ = (!crate::leanh::lean_is_exclusive(v___x_3031_)) as u8;
                    if v_isSharedCheck_3054_ == 0 {
                        v___x_3034_ = v___x_3031_;
                        v_isShared_3035_ = v_isSharedCheck_3054_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3032_);
                        crate::leanh::lean_dec(v___x_3031_);
                        v___x_3034_ = crate::leanh::lean_box(0);
                        v_isShared_3035_ = v_isSharedCheck_3054_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3055_ = crate::leanh::lean_ctor_get(v___x_3031_, 0);
                    v_isSharedCheck_3062_ = (!crate::leanh::lean_is_exclusive(v___x_3031_)) as u8;
                    if v_isSharedCheck_3062_ == 0 {
                        v___x_3057_ = v___x_3031_;
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3055_);
                        crate::leanh::lean_dec(v___x_3031_);
                        v___x_3057_ = crate::leanh::lean_box(0);
                        v_isShared_3058_ = v_isSharedCheck_3062_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3032_) == 0 {
                    v___x_3036_ = crate::leanh::lean_box(0);
                    if v_isShared_3035_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3034_, 0, v___x_3036_);
                        v___x_3038_ = v___x_3034_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3036_);
                        v___x_3038_ = v_reuseFailAlloc_3039_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3040_ = crate::leanh::lean_ctor_get(v_a_3032_, 0);
                    v_isSharedCheck_3053_ = (!crate::leanh::lean_is_exclusive(v_a_3032_)) as u8;
                    if v_isSharedCheck_3053_ == 0 {
                        v___x_3042_ = v_a_3032_;
                        v_isShared_3043_ = v_isSharedCheck_3053_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3040_);
                        crate::leanh::lean_dec(v_a_3032_);
                        v___x_3042_ = crate::leanh::lean_box(0);
                        v_isShared_3043_ = v_isSharedCheck_3053_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3038_;
            }
            3 => {
                v_fst_3044_ = crate::leanh::lean_ctor_get(v_val_3040_, 0);
                crate::leanh::lean_inc(v_fst_3044_);
                crate::leanh::lean_dec(v_val_3040_);
                v___x_3045_ = lean_uint16_of_nat(v_fst_3044_);
                crate::leanh::lean_dec(v_fst_3044_);
                v___x_3046_ = crate::leanh::lean_box((v___x_3045_) as usize);
                if v_isShared_3043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3042_, 0, v___x_3046_);
                    v___x_3048_ = v___x_3042_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3052_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v___x_3046_);
                    v___x_3048_ = v_reuseFailAlloc_3052_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3035_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3034_, 0, v___x_3048_);
                    v___x_3050_ = v___x_3034_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3051_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
                    v___x_3050_ = v_reuseFailAlloc_3051_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3050_;
            }
            6 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUInt16Value_x3f___boxed(
    mut v_e_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
    mut v_a_3065_: *mut crate::leanh::LeanObject,
    mut v_a_3066_: *mut crate::leanh::LeanObject,
    mut v_a_3067_: *mut crate::leanh::LeanObject,
    mut v_a_3068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3069_ =
        l_Lean_Meta_getUInt16Value_x3f(v_e_3063_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
    crate::leanh::lean_dec(v_a_3067_);
    crate::leanh::lean_dec_ref(v_a_3066_);
    crate::leanh::lean_dec(v_a_3065_);
    crate::leanh::lean_dec_ref(v_a_3064_);
    return v_res_3069_;
}
pub unsafe fn l_Lean_Meta_getUInt32Value_x3f(
    mut v_e_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v_a_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
    mut v_a_3077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v_fst_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u32 = 0;
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3102_: u8 = 0;
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_a_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3079_ = l_Lean_Meta_getUInt32Value_x3f___closed__1;
                v___x_3080_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_3073_,
                    v___x_3079_,
                    v_a_3074_,
                    v_a_3075_,
                    v_a_3076_,
                    v_a_3077_,
                );
                if crate::leanh::lean_obj_tag(v___x_3080_) == 0 {
                    v_a_3081_ = crate::leanh::lean_ctor_get(v___x_3080_, 0);
                    v_isSharedCheck_3103_ = (!crate::leanh::lean_is_exclusive(v___x_3080_)) as u8;
                    if v_isSharedCheck_3103_ == 0 {
                        v___x_3083_ = v___x_3080_;
                        v_isShared_3084_ = v_isSharedCheck_3103_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3081_);
                        crate::leanh::lean_dec(v___x_3080_);
                        v___x_3083_ = crate::leanh::lean_box(0);
                        v_isShared_3084_ = v_isSharedCheck_3103_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3104_ = crate::leanh::lean_ctor_get(v___x_3080_, 0);
                    v_isSharedCheck_3111_ = (!crate::leanh::lean_is_exclusive(v___x_3080_)) as u8;
                    if v_isSharedCheck_3111_ == 0 {
                        v___x_3106_ = v___x_3080_;
                        v_isShared_3107_ = v_isSharedCheck_3111_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3104_);
                        crate::leanh::lean_dec(v___x_3080_);
                        v___x_3106_ = crate::leanh::lean_box(0);
                        v_isShared_3107_ = v_isSharedCheck_3111_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3081_) == 0 {
                    v___x_3085_ = crate::leanh::lean_box(0);
                    if v_isShared_3084_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3083_, 0, v___x_3085_);
                        v___x_3087_ = v___x_3083_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
                        v___x_3087_ = v_reuseFailAlloc_3088_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3089_ = crate::leanh::lean_ctor_get(v_a_3081_, 0);
                    v_isSharedCheck_3102_ = (!crate::leanh::lean_is_exclusive(v_a_3081_)) as u8;
                    if v_isSharedCheck_3102_ == 0 {
                        v___x_3091_ = v_a_3081_;
                        v_isShared_3092_ = v_isSharedCheck_3102_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3089_);
                        crate::leanh::lean_dec(v_a_3081_);
                        v___x_3091_ = crate::leanh::lean_box(0);
                        v_isShared_3092_ = v_isSharedCheck_3102_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3087_;
            }
            3 => {
                v_fst_3093_ = crate::leanh::lean_ctor_get(v_val_3089_, 0);
                crate::leanh::lean_inc(v_fst_3093_);
                crate::leanh::lean_dec(v_val_3089_);
                v___x_3094_ = lean_uint32_of_nat(v_fst_3093_);
                crate::leanh::lean_dec(v_fst_3093_);
                v___x_3095_ = crate::leanh::lean_box_uint32(v___x_3094_);
                if v_isShared_3092_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3091_, 0, v___x_3095_);
                    v___x_3097_ = v___x_3091_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3095_);
                    v___x_3097_ = v_reuseFailAlloc_3101_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3084_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3083_, 0, v___x_3097_);
                    v___x_3099_ = v___x_3083_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3099_;
            }
            6 => {
                if v_isShared_3107_ == 0 {
                    v___x_3109_ = v___x_3106_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3110_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
                    v___x_3109_ = v_reuseFailAlloc_3110_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUInt32Value_x3f___boxed(
    mut v_e_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
    mut v_a_3114_: *mut crate::leanh::LeanObject,
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
    mut v_a_3117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3118_ =
        l_Lean_Meta_getUInt32Value_x3f(v_e_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_);
    crate::leanh::lean_dec(v_a_3116_);
    crate::leanh::lean_dec_ref(v_a_3115_);
    crate::leanh::lean_dec(v_a_3114_);
    crate::leanh::lean_dec_ref(v_a_3113_);
    return v_res_3118_;
}
pub unsafe fn l_Lean_Meta_getUInt64Value_x3f(
    mut v_e_3122_: *mut crate::leanh::LeanObject,
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v_a_3124_: *mut crate::leanh::LeanObject,
    mut v_a_3125_: *mut crate::leanh::LeanObject,
    mut v_a_3126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3141_: u8 = 0;
    let mut v_fst_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u64 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_a_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3128_ = l_Lean_Meta_getUInt64Value_x3f___closed__1;
                v___x_3129_ = l_Lean_Meta_getOfNatValue_x3f(
                    v_e_3122_,
                    v___x_3128_,
                    v_a_3123_,
                    v_a_3124_,
                    v_a_3125_,
                    v_a_3126_,
                );
                if crate::leanh::lean_obj_tag(v___x_3129_) == 0 {
                    v_a_3130_ = crate::leanh::lean_ctor_get(v___x_3129_, 0);
                    v_isSharedCheck_3152_ = (!crate::leanh::lean_is_exclusive(v___x_3129_)) as u8;
                    if v_isSharedCheck_3152_ == 0 {
                        v___x_3132_ = v___x_3129_;
                        v_isShared_3133_ = v_isSharedCheck_3152_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3130_);
                        crate::leanh::lean_dec(v___x_3129_);
                        v___x_3132_ = crate::leanh::lean_box(0);
                        v_isShared_3133_ = v_isSharedCheck_3152_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3153_ = crate::leanh::lean_ctor_get(v___x_3129_, 0);
                    v_isSharedCheck_3160_ = (!crate::leanh::lean_is_exclusive(v___x_3129_)) as u8;
                    if v_isSharedCheck_3160_ == 0 {
                        v___x_3155_ = v___x_3129_;
                        v_isShared_3156_ = v_isSharedCheck_3160_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3153_);
                        crate::leanh::lean_dec(v___x_3129_);
                        v___x_3155_ = crate::leanh::lean_box(0);
                        v_isShared_3156_ = v_isSharedCheck_3160_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3130_) == 0 {
                    v___x_3134_ = crate::leanh::lean_box(0);
                    if v_isShared_3133_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3132_, 0, v___x_3134_);
                        v___x_3136_ = v___x_3132_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
                        v___x_3136_ = v_reuseFailAlloc_3137_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_3138_ = crate::leanh::lean_ctor_get(v_a_3130_, 0);
                    v_isSharedCheck_3151_ = (!crate::leanh::lean_is_exclusive(v_a_3130_)) as u8;
                    if v_isSharedCheck_3151_ == 0 {
                        v___x_3140_ = v_a_3130_;
                        v_isShared_3141_ = v_isSharedCheck_3151_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3138_);
                        crate::leanh::lean_dec(v_a_3130_);
                        v___x_3140_ = crate::leanh::lean_box(0);
                        v_isShared_3141_ = v_isSharedCheck_3151_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3136_;
            }
            3 => {
                v_fst_3142_ = crate::leanh::lean_ctor_get(v_val_3138_, 0);
                crate::leanh::lean_inc(v_fst_3142_);
                crate::leanh::lean_dec(v_val_3138_);
                v___x_3143_ = lean_uint64_of_nat(v_fst_3142_);
                crate::leanh::lean_dec(v_fst_3142_);
                v___x_3144_ = crate::leanh::lean_box_uint64(v___x_3143_);
                if v_isShared_3141_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3140_, 0, v___x_3144_);
                    v___x_3146_ = v___x_3140_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3144_);
                    v___x_3146_ = v_reuseFailAlloc_3150_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3132_, 0, v___x_3146_);
                    v___x_3148_ = v___x_3132_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
                    v___x_3148_ = v_reuseFailAlloc_3149_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3148_;
            }
            6 => {
                if v_isShared_3156_ == 0 {
                    v___x_3158_ = v___x_3155_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
                    v___x_3158_ = v_reuseFailAlloc_3159_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUInt64Value_x3f___boxed(
    mut v_e_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
    mut v_a_3164_: *mut crate::leanh::LeanObject,
    mut v_a_3165_: *mut crate::leanh::LeanObject,
    mut v_a_3166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3167_ =
        l_Lean_Meta_getUInt64Value_x3f(v_e_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
    crate::leanh::lean_dec(v_a_3165_);
    crate::leanh::lean_dec_ref(v_a_3164_);
    crate::leanh::lean_dec(v_a_3163_);
    crate::leanh::lean_dec_ref(v_a_3162_);
    return v_res_3167_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
    mut v_e_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut v_unused_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3171_ = l_Lean_Expr_hasMVar(v_e_3168_);
                if v___x_3171_ == 0 {
                    v___x_3172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3172_, 0, v_e_3168_);
                    return v___x_3172_;
                } else {
                    v___x_3173_ = lean_st_ref_get(v___y_3169_);
                    v_mctx_3174_ = crate::leanh::lean_ctor_get(v___x_3173_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3174_);
                    crate::leanh::lean_dec(v___x_3173_);
                    v___x_3175_ = l_Lean_instantiateMVarsCore(v_mctx_3174_, v_e_3168_);
                    v_fst_3176_ = crate::leanh::lean_ctor_get(v___x_3175_, 0);
                    crate::leanh::lean_inc(v_fst_3176_);
                    v_snd_3177_ = crate::leanh::lean_ctor_get(v___x_3175_, 1);
                    crate::leanh::lean_inc(v_snd_3177_);
                    crate::leanh::lean_dec_ref(v___x_3175_);
                    v___x_3178_ = lean_st_ref_take(v___y_3169_);
                    v_cache_3179_ = crate::leanh::lean_ctor_get(v___x_3178_, 1);
                    v_zetaDeltaFVarIds_3180_ = crate::leanh::lean_ctor_get(v___x_3178_, 2);
                    v_postponed_3181_ = crate::leanh::lean_ctor_get(v___x_3178_, 3);
                    v_diag_3182_ = crate::leanh::lean_ctor_get(v___x_3178_, 4);
                    v_isSharedCheck_3191_ = (!crate::leanh::lean_is_exclusive(v___x_3178_)) as u8;
                    if v_isSharedCheck_3191_ == 0 {
                        v_unused_3192_ = crate::leanh::lean_ctor_get(v___x_3178_, 0);
                        crate::leanh::lean_dec(v_unused_3192_);
                        v___x_3184_ = v___x_3178_;
                        v_isShared_3185_ = v_isSharedCheck_3191_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3182_);
                        crate::leanh::lean_inc(v_postponed_3181_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3180_);
                        crate::leanh::lean_inc(v_cache_3179_);
                        crate::leanh::lean_dec(v___x_3178_);
                        v___x_3184_ = crate::leanh::lean_box(0);
                        v_isShared_3185_ = v_isSharedCheck_3191_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3185_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3184_, 0, v_snd_3177_);
                    v___x_3187_ = v___x_3184_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_snd_3177_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_cache_3179_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3190_,
                        2,
                        v_zetaDeltaFVarIds_3180_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 3, v_postponed_3181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 4, v_diag_3182_);
                    v___x_3187_ = v_reuseFailAlloc_3190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3188_ = lean_st_ref_set(v___y_3169_, v___x_3187_);
                v___x_3189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3189_, 0, v_fst_3176_);
                return v___x_3189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg___boxed(
    mut v_e_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3196_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
        v_e_3193_,
        v___y_3194_,
    );
    crate::leanh::lean_dec(v___y_3194_);
    return v_res_3196_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(
    mut v_e_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3203_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
        v_e_3197_,
        v___y_3199_,
    );
    return v___x_3203_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___boxed(
    mut v_e_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3210_ = l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0(
        v_e_3204_,
        v___y_3205_,
        v___y_3206_,
        v___y_3207_,
        v___y_3208_,
    );
    crate::leanh::lean_dec(v___y_3208_);
    crate::leanh::lean_dec_ref(v___y_3207_);
    crate::leanh::lean_dec(v___y_3206_);
    crate::leanh::lean_dec_ref(v___y_3205_);
    return v_res_3210_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3211_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3212_ = lean_nat_to_int(v___x_3211_);
    return v___x_3212_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3213_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3214_ = l_Lean_Level_ofNat(v___x_3213_);
    return v___x_3214_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3215_ = crate::leanh::lean_box(0);
    v___x_3216_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__1_once),
        _init_l_Lean_Meta_normLitValue___closed__1,
    );
    v___x_3217_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3217_, 0, v___x_3216_);
    crate::leanh::lean_ctor_set(v___x_3217_, 1, v___x_3215_);
    return v___x_3217_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3218_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__2_once),
        _init_l_Lean_Meta_normLitValue___closed__2,
    );
    v___x_3219_ = l_Lean_Meta_getIntValue_x3f___closed__4;
    v___x_3220_ = l_Lean_Expr_const___override(v___x_3219_, v___x_3218_);
    return v___x_3220_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3221_ = crate::leanh::lean_box(0);
    v___x_3222_ = l_Lean_Meta_getIntValue_x3f___closed__1;
    v___x_3223_ = l_Lean_Expr_const___override(v___x_3222_, v___x_3221_);
    return v___x_3223_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3228_ = crate::leanh::lean_box(0);
    v___x_3229_ = l_Lean_Meta_normLitValue___closed__6;
    v___x_3230_ = l_Lean_Expr_const___override(v___x_3229_, v___x_3228_);
    return v___x_3230_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3231_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__2_once),
        _init_l_Lean_Meta_normLitValue___closed__2,
    );
    v___x_3232_ = l_Lean_Meta_getOfNatValue_x3f___closed__2;
    v___x_3233_ = l_Lean_Expr_const___override(v___x_3232_, v___x_3231_);
    return v___x_3233_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3234_ = crate::leanh::lean_box(0);
    v___x_3235_ = l_Lean_Meta_getFinValue_x3f___closed__1;
    v___x_3236_ = l_Lean_mkConst(v___x_3235_, v___x_3234_);
    return v___x_3236_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3241_ = crate::leanh::lean_box(0);
    v___x_3242_ = l_Lean_Meta_normLitValue___closed__11;
    v___x_3243_ = l_Lean_Expr_const___override(v___x_3242_, v___x_3241_);
    return v___x_3243_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3248_ = crate::leanh::lean_box(0);
    v___x_3249_ = l_Lean_Meta_normLitValue___closed__14;
    v___x_3250_ = l_Lean_Expr_const___override(v___x_3249_, v___x_3248_);
    return v___x_3250_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3251_ = crate::leanh::lean_box(0);
    v___x_3252_ = l_Lean_Meta_getBitVecValue_x3f___closed__2;
    v___x_3253_ = l_Lean_Expr_const___override(v___x_3252_, v___x_3251_);
    return v___x_3253_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3254_ = crate::leanh::lean_box(0);
    v___x_3255_ = l_Lean_Meta_getCharValue_x3f___closed__1;
    v___x_3256_ = l_Lean_mkConst(v___x_3255_, v___x_3254_);
    return v___x_3256_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__18() -> *mut crate::leanh::LeanObject {
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3257_ = crate::leanh::lean_box(0);
    v___x_3258_ = l_Lean_Meta_getUInt8Value_x3f___closed__1;
    v___x_3259_ = l_Lean_mkConst(v___x_3258_, v___x_3257_);
    return v___x_3259_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__20() -> *mut crate::leanh::LeanObject {
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3263_ = crate::leanh::lean_box(0);
    v___x_3264_ = l_Lean_Meta_normLitValue___closed__19;
    v___x_3265_ = l_Lean_Expr_const___override(v___x_3264_, v___x_3263_);
    return v___x_3265_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3266_ = crate::leanh::lean_box(0);
    v___x_3267_ = l_Lean_Meta_getUInt16Value_x3f___closed__1;
    v___x_3268_ = l_Lean_mkConst(v___x_3267_, v___x_3266_);
    return v___x_3268_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__23() -> *mut crate::leanh::LeanObject {
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3272_ = crate::leanh::lean_box(0);
    v___x_3273_ = l_Lean_Meta_normLitValue___closed__22;
    v___x_3274_ = l_Lean_Expr_const___override(v___x_3273_, v___x_3272_);
    return v___x_3274_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3275_ = crate::leanh::lean_box(0);
    v___x_3276_ = l_Lean_Meta_getUInt32Value_x3f___closed__1;
    v___x_3277_ = l_Lean_mkConst(v___x_3276_, v___x_3275_);
    return v___x_3277_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__26() -> *mut crate::leanh::LeanObject {
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3281_ = crate::leanh::lean_box(0);
    v___x_3282_ = l_Lean_Meta_normLitValue___closed__25;
    v___x_3283_ = l_Lean_Expr_const___override(v___x_3282_, v___x_3281_);
    return v___x_3283_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3284_ = crate::leanh::lean_box(0);
    v___x_3285_ = l_Lean_Meta_getUInt64Value_x3f___closed__1;
    v___x_3286_ = l_Lean_mkConst(v___x_3285_, v___x_3284_);
    return v___x_3286_;
}
pub unsafe fn _init_l_Lean_Meta_normLitValue___closed__29() -> *mut crate::leanh::LeanObject {
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3290_ = crate::leanh::lean_box(0);
    v___x_3291_ = l_Lean_Meta_normLitValue___closed__28;
    v___x_3292_ = l_Lean_Expr_const___override(v___x_3291_, v___x_3290_);
    return v___x_3292_;
}
pub unsafe fn l_Lean_Meta_normLitValue(
    mut v_e_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
    mut v_a_3295_: *mut crate::leanh::LeanObject,
    mut v_a_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3305_: u8 = 0;
    let mut v_val_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3315_: u8 = 0;
    let mut v_val_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v_val_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v_val_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v_val_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: u32 = 0;
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3397_: u8 = 0;
    let mut v_val_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3414_: u8 = 0;
    let mut v_val_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: u16 = 0;
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3431_: u8 = 0;
    let mut v_val_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: u32 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3448_: u8 = 0;
    let mut v_val_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: u64 = 0;
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v_a_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3468_: u8 = 0;
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3472_: u8 = 0;
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut v_a_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3477_: u8 = 0;
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3481_: u8 = 0;
    let mut v_isSharedCheck_3482_: u8 = 0;
    let mut v_a_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3486_: u8 = 0;
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut v_isSharedCheck_3491_: u8 = 0;
    let mut v_a_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3495_: u8 = 0;
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3499_: u8 = 0;
    let mut v_isSharedCheck_3500_: u8 = 0;
    let mut v_a_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3508_: u8 = 0;
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut v_a_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_isSharedCheck_3518_: u8 = 0;
    let mut v_a_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3526_: u8 = 0;
    let mut v_isSharedCheck_3527_: u8 = 0;
    let mut v_a_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3535_: u8 = 0;
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut v_a_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3540_: u8 = 0;
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3299_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
                        v_e_3293_, v_a_3295_,
                    );
                v_a_3300_ = crate::leanh::lean_ctor_get(v___x_3299_, 0);
                crate::leanh::lean_inc(v_a_3300_);
                crate::leanh::lean_dec_ref(v___x_3299_);
                v___x_3301_ = l_Lean_Meta_getNatValue_x3f(
                    v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                );
                if crate::leanh::lean_obj_tag(v___x_3301_) == 0 {
                    v_a_3302_ = crate::leanh::lean_ctor_get(v___x_3301_, 0);
                    v_isSharedCheck_3536_ = (!crate::leanh::lean_is_exclusive(v___x_3301_)) as u8;
                    if v_isSharedCheck_3536_ == 0 {
                        v___x_3304_ = v___x_3301_;
                        v_isShared_3305_ = v_isSharedCheck_3536_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3302_);
                        crate::leanh::lean_dec(v___x_3301_);
                        v___x_3304_ = crate::leanh::lean_box(0);
                        v_isShared_3305_ = v_isSharedCheck_3536_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_a_3537_ = crate::leanh::lean_ctor_get(v___x_3301_, 0);
                    v_isSharedCheck_3544_ = (!crate::leanh::lean_is_exclusive(v___x_3301_)) as u8;
                    if v_isSharedCheck_3544_ == 0 {
                        v___x_3539_ = v___x_3301_;
                        v_isShared_3540_ = v_isSharedCheck_3544_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3537_);
                        crate::leanh::lean_dec(v___x_3301_);
                        v___x_3539_ = crate::leanh::lean_box(0);
                        v_isShared_3540_ = v_isSharedCheck_3544_;
                        state = 38;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3302_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3306_ = crate::leanh::lean_ctor_get(v_a_3302_, 0);
                    crate::leanh::lean_inc(v_val_3306_);
                    crate::leanh::lean_dec_ref_known(v_a_3302_, 1);
                    v___x_3307_ = l_Lean_mkNatLit(v_val_3306_);
                    if v_isShared_3305_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3304_, 0, v___x_3307_);
                        v___x_3309_ = v___x_3304_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3310_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
                        v___x_3309_ = v_reuseFailAlloc_3310_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3304_);
                    crate::leanh::lean_dec(v_a_3302_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3311_ = l_Lean_Meta_getIntValue_x3f(
                        v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3311_) == 0 {
                        v_a_3312_ = crate::leanh::lean_ctor_get(v___x_3311_, 0);
                        v_isSharedCheck_3527_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3311_)) as u8;
                        if v_isSharedCheck_3527_ == 0 {
                            v___x_3314_ = v___x_3311_;
                            v_isShared_3315_ = v_isSharedCheck_3527_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3312_);
                            crate::leanh::lean_dec(v___x_3311_);
                            v___x_3314_ = crate::leanh::lean_box(0);
                            v_isShared_3315_ = v_isSharedCheck_3527_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_a_3528_ = crate::leanh::lean_ctor_get(v___x_3311_, 0);
                        v_isSharedCheck_3535_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3311_)) as u8;
                        if v_isSharedCheck_3535_ == 0 {
                            v___x_3530_ = v___x_3311_;
                            v_isShared_3531_ = v_isSharedCheck_3535_;
                            state = 36;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3528_);
                            crate::leanh::lean_dec(v___x_3311_);
                            v___x_3530_ = crate::leanh::lean_box(0);
                            v_isShared_3531_ = v_isSharedCheck_3535_;
                            state = 36;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3309_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3312_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3316_ = crate::leanh::lean_ctor_get(v_a_3312_, 0);
                    crate::leanh::lean_inc(v_val_3316_);
                    crate::leanh::lean_dec_ref_known(v_a_3312_, 1);
                    v___x_3317_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__0_once),
                        _init_l_Lean_Meta_normLitValue___closed__0,
                    );
                    v___x_3318_ = lean_int_dec_le(v___x_3317_, v_val_3316_);
                    if v___x_3318_ == 0 {
                        v___x_3319_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__3_once),
                            _init_l_Lean_Meta_normLitValue___closed__3,
                        );
                        v___x_3320_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__4_once),
                            _init_l_Lean_Meta_normLitValue___closed__4,
                        );
                        v___x_3321_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__7_once),
                            _init_l_Lean_Meta_normLitValue___closed__7,
                        );
                        v___x_3322_ = lean_int_neg(v_val_3316_);
                        crate::leanh::lean_dec(v_val_3316_);
                        v___x_3323_ = l_Int_toNat(v___x_3322_);
                        crate::leanh::lean_dec(v___x_3322_);
                        v___x_3324_ = l_Lean_instToExprInt_mkNat(v___x_3323_);
                        v___x_3325_ =
                            l_Lean_mkApp3(v___x_3319_, v___x_3320_, v___x_3321_, v___x_3324_);
                        if v_isShared_3315_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3314_, 0, v___x_3325_);
                            v___x_3327_ = v___x_3314_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3328_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3328_, 0, v___x_3325_);
                            v___x_3327_ = v_reuseFailAlloc_3328_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_3329_ = l_Int_toNat(v_val_3316_);
                        crate::leanh::lean_dec(v_val_3316_);
                        v___x_3330_ = l_Lean_instToExprInt_mkNat(v___x_3329_);
                        if v_isShared_3315_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3314_, 0, v___x_3330_);
                            v___x_3332_ = v___x_3314_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3333_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
                            v___x_3332_ = v_reuseFailAlloc_3333_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3314_);
                    crate::leanh::lean_dec(v_a_3312_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3334_ = l_Lean_Meta_getFinValue_x3f(
                        v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3334_) == 0 {
                        v_a_3335_ = crate::leanh::lean_ctor_get(v___x_3334_, 0);
                        v_isSharedCheck_3518_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3334_)) as u8;
                        if v_isSharedCheck_3518_ == 0 {
                            v___x_3337_ = v___x_3334_;
                            v_isShared_3338_ = v_isSharedCheck_3518_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3335_);
                            crate::leanh::lean_dec(v___x_3334_);
                            v___x_3337_ = crate::leanh::lean_box(0);
                            v_isShared_3338_ = v_isSharedCheck_3518_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_a_3519_ = crate::leanh::lean_ctor_get(v___x_3334_, 0);
                        v_isSharedCheck_3526_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3334_)) as u8;
                        if v_isSharedCheck_3526_ == 0 {
                            v___x_3521_ = v___x_3334_;
                            v_isShared_3522_ = v_isSharedCheck_3526_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3519_);
                            crate::leanh::lean_dec(v___x_3334_);
                            v___x_3521_ = crate::leanh::lean_box(0);
                            v_isShared_3522_ = v_isSharedCheck_3526_;
                            state = 34;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_3327_;
            }
            5 => {
                return v___x_3332_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_3335_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3339_ = crate::leanh::lean_ctor_get(v_a_3335_, 0);
                    crate::leanh::lean_inc(v_val_3339_);
                    crate::leanh::lean_dec_ref_known(v_a_3335_, 1);
                    v_fst_3340_ = crate::leanh::lean_ctor_get(v_val_3339_, 0);
                    crate::leanh::lean_inc_n(v_fst_3340_, 2);
                    v_snd_3341_ = crate::leanh::lean_ctor_get(v_val_3339_, 1);
                    crate::leanh::lean_inc(v_snd_3341_);
                    crate::leanh::lean_dec(v_val_3339_);
                    v_r_3342_ = l_Lean_mkRawNatLit(v_snd_3341_);
                    v___x_3343_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8_once),
                        _init_l_Lean_Meta_normLitValue___closed__8,
                    );
                    v___x_3344_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__9_once),
                        _init_l_Lean_Meta_normLitValue___closed__9,
                    );
                    v___x_3345_ = l_Lean_mkNatLit(v_fst_3340_);
                    crate::leanh::lean_inc_ref(v___x_3345_);
                    v___x_3346_ = l_Lean_Expr_app___override(v___x_3344_, v___x_3345_);
                    v___x_3347_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__12),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__12_once),
                        _init_l_Lean_Meta_normLitValue___closed__12,
                    );
                    v___x_3348_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__15_once),
                        _init_l_Lean_Meta_normLitValue___closed__15,
                    );
                    v___x_3349_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3350_ = lean_nat_sub(v_fst_3340_, v___x_3349_);
                    crate::leanh::lean_dec(v_fst_3340_);
                    v___x_3351_ = l_Lean_mkNatLit(v___x_3350_);
                    v___x_3352_ = l_Lean_Expr_app___override(v___x_3348_, v___x_3351_);
                    crate::leanh::lean_inc_ref(v_r_3342_);
                    v___x_3353_ = l_Lean_mkApp3(v___x_3347_, v___x_3345_, v___x_3352_, v_r_3342_);
                    v___x_3354_ = l_Lean_mkApp3(v___x_3343_, v___x_3346_, v_r_3342_, v___x_3353_);
                    if v_isShared_3338_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3337_, 0, v___x_3354_);
                        v___x_3356_ = v___x_3337_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3357_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
                        v___x_3356_ = v_reuseFailAlloc_3357_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3337_);
                    crate::leanh::lean_dec(v_a_3335_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3358_ = l_Lean_Meta_getBitVecValue_x3f(
                        v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3358_) == 0 {
                        v_a_3359_ = crate::leanh::lean_ctor_get(v___x_3358_, 0);
                        v_isSharedCheck_3509_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3358_)) as u8;
                        if v_isSharedCheck_3509_ == 0 {
                            v___x_3361_ = v___x_3358_;
                            v_isShared_3362_ = v_isSharedCheck_3509_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3359_);
                            crate::leanh::lean_dec(v___x_3358_);
                            v___x_3361_ = crate::leanh::lean_box(0);
                            v_isShared_3362_ = v_isSharedCheck_3509_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_a_3510_ = crate::leanh::lean_ctor_get(v___x_3358_, 0);
                        v_isSharedCheck_3517_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3358_)) as u8;
                        if v_isSharedCheck_3517_ == 0 {
                            v___x_3512_ = v___x_3358_;
                            v_isShared_3513_ = v_isSharedCheck_3517_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3510_);
                            crate::leanh::lean_dec(v___x_3358_);
                            v___x_3512_ = crate::leanh::lean_box(0);
                            v_isShared_3513_ = v_isSharedCheck_3517_;
                            state = 32;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_3356_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_3359_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3363_ = crate::leanh::lean_ctor_get(v_a_3359_, 0);
                    crate::leanh::lean_inc(v_val_3363_);
                    crate::leanh::lean_dec_ref_known(v_a_3359_, 1);
                    v_fst_3364_ = crate::leanh::lean_ctor_get(v_val_3363_, 0);
                    crate::leanh::lean_inc(v_fst_3364_);
                    v_snd_3365_ = crate::leanh::lean_ctor_get(v_val_3363_, 1);
                    crate::leanh::lean_inc(v_snd_3365_);
                    crate::leanh::lean_dec(v_val_3363_);
                    v___x_3366_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__16),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__16_once),
                        _init_l_Lean_Meta_normLitValue___closed__16,
                    );
                    v___x_3367_ = l_Lean_mkNatLit(v_fst_3364_);
                    v___x_3368_ = l_Lean_mkNatLit(v_snd_3365_);
                    v___x_3369_ = l_Lean_mkAppB(v___x_3366_, v___x_3367_, v___x_3368_);
                    if v_isShared_3362_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3369_);
                        v___x_3371_ = v___x_3361_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
                        v___x_3371_ = v_reuseFailAlloc_3372_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3359_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3373_ = l_Lean_Meta_getStringValue_x3f(v_a_3300_);
                    if crate::leanh::lean_obj_tag(v___x_3373_) == 1 {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_val_3374_ = crate::leanh::lean_ctor_get(v___x_3373_, 0);
                        crate::leanh::lean_inc(v_val_3374_);
                        crate::leanh::lean_dec_ref_known(v___x_3373_, 1);
                        v___x_3375_ = l_Lean_mkStrLit(v_val_3374_);
                        if v_isShared_3362_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3375_);
                            v___x_3377_ = v___x_3361_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_3378_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
                            v___x_3377_ = v_reuseFailAlloc_3378_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3373_);
                        crate::leanh::lean_del_object(v___x_3361_);
                        crate::leanh::lean_inc(v_a_3300_);
                        v___x_3379_ = l_Lean_Meta_getCharValue_x3f(
                            v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3379_) == 0 {
                            v_a_3380_ = crate::leanh::lean_ctor_get(v___x_3379_, 0);
                            v_isSharedCheck_3500_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3379_)) as u8;
                            if v_isSharedCheck_3500_ == 0 {
                                v___x_3382_ = v___x_3379_;
                                v_isShared_3383_ = v_isSharedCheck_3500_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3380_);
                                crate::leanh::lean_dec(v___x_3379_);
                                v___x_3382_ = crate::leanh::lean_box(0);
                                v_isShared_3383_ = v_isSharedCheck_3500_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3300_);
                            v_a_3501_ = crate::leanh::lean_ctor_get(v___x_3379_, 0);
                            v_isSharedCheck_3508_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3379_)) as u8;
                            if v_isSharedCheck_3508_ == 0 {
                                v___x_3503_ = v___x_3379_;
                                v_isShared_3504_ = v_isSharedCheck_3508_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3501_);
                                crate::leanh::lean_dec(v___x_3379_);
                                v___x_3503_ = crate::leanh::lean_box(0);
                                v_isShared_3504_ = v_isSharedCheck_3508_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                }
            }
            9 => {
                return v___x_3371_;
            }
            10 => {
                return v___x_3377_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_a_3380_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3384_ = crate::leanh::lean_ctor_get(v_a_3380_, 0);
                    crate::leanh::lean_inc(v_val_3384_);
                    crate::leanh::lean_dec_ref_known(v_a_3380_, 1);
                    v___x_3385_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__17),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__17_once),
                        _init_l_Lean_Meta_normLitValue___closed__17,
                    );
                    v___x_3386_ = crate::leanh::lean_unbox_uint32(v_val_3384_);
                    crate::leanh::lean_dec(v_val_3384_);
                    v___x_3387_ = lean_uint32_to_nat(v___x_3386_);
                    v___x_3388_ = l_Lean_mkRawNatLit(v___x_3387_);
                    v___x_3389_ = l_Lean_Expr_app___override(v___x_3385_, v___x_3388_);
                    if v_isShared_3383_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3382_, 0, v___x_3389_);
                        v___x_3391_ = v___x_3382_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3392_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
                        v___x_3391_ = v_reuseFailAlloc_3392_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3382_);
                    crate::leanh::lean_dec(v_a_3380_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3393_ = l_Lean_Meta_getUInt8Value_x3f(
                        v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3393_) == 0 {
                        v_a_3394_ = crate::leanh::lean_ctor_get(v___x_3393_, 0);
                        v_isSharedCheck_3491_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3393_)) as u8;
                        if v_isSharedCheck_3491_ == 0 {
                            v___x_3396_ = v___x_3393_;
                            v_isShared_3397_ = v_isSharedCheck_3491_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3394_);
                            crate::leanh::lean_dec(v___x_3393_);
                            v___x_3396_ = crate::leanh::lean_box(0);
                            v_isShared_3397_ = v_isSharedCheck_3491_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_a_3492_ = crate::leanh::lean_ctor_get(v___x_3393_, 0);
                        v_isSharedCheck_3499_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3393_)) as u8;
                        if v_isSharedCheck_3499_ == 0 {
                            v___x_3494_ = v___x_3393_;
                            v_isShared_3495_ = v_isSharedCheck_3499_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3492_);
                            crate::leanh::lean_dec(v___x_3393_);
                            v___x_3494_ = crate::leanh::lean_box(0);
                            v_isShared_3495_ = v_isSharedCheck_3499_;
                            state = 28;
                            continue;
                        }
                    }
                }
            }
            12 => {
                return v___x_3391_;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_a_3394_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3398_ = crate::leanh::lean_ctor_get(v_a_3394_, 0);
                    crate::leanh::lean_inc(v_val_3398_);
                    crate::leanh::lean_dec_ref_known(v_a_3394_, 1);
                    v___x_3399_ = (crate::leanh::lean_unbox(v_val_3398_) as u8);
                    crate::leanh::lean_dec(v_val_3398_);
                    v___x_3400_ = lean_uint8_to_nat(v___x_3399_);
                    v_r_3401_ = l_Lean_mkRawNatLit(v___x_3400_);
                    v___x_3402_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8_once),
                        _init_l_Lean_Meta_normLitValue___closed__8,
                    );
                    v___x_3403_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__18),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__18_once),
                        _init_l_Lean_Meta_normLitValue___closed__18,
                    );
                    v___x_3404_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__20),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__20_once),
                        _init_l_Lean_Meta_normLitValue___closed__20,
                    );
                    crate::leanh::lean_inc_ref(v_r_3401_);
                    v___x_3405_ = l_Lean_Expr_app___override(v___x_3404_, v_r_3401_);
                    v___x_3406_ = l_Lean_mkApp3(v___x_3402_, v___x_3403_, v_r_3401_, v___x_3405_);
                    if v_isShared_3397_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3396_, 0, v___x_3406_);
                        v___x_3408_ = v___x_3396_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
                        v___x_3408_ = v_reuseFailAlloc_3409_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3396_);
                    crate::leanh::lean_dec(v_a_3394_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3410_ = l_Lean_Meta_getUInt16Value_x3f(
                        v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3410_) == 0 {
                        v_a_3411_ = crate::leanh::lean_ctor_get(v___x_3410_, 0);
                        v_isSharedCheck_3482_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3410_)) as u8;
                        if v_isSharedCheck_3482_ == 0 {
                            v___x_3413_ = v___x_3410_;
                            v_isShared_3414_ = v_isSharedCheck_3482_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3411_);
                            crate::leanh::lean_dec(v___x_3410_);
                            v___x_3413_ = crate::leanh::lean_box(0);
                            v_isShared_3414_ = v_isSharedCheck_3482_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_a_3483_ = crate::leanh::lean_ctor_get(v___x_3410_, 0);
                        v_isSharedCheck_3490_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3410_)) as u8;
                        if v_isSharedCheck_3490_ == 0 {
                            v___x_3485_ = v___x_3410_;
                            v_isShared_3486_ = v_isSharedCheck_3490_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3483_);
                            crate::leanh::lean_dec(v___x_3410_);
                            v___x_3485_ = crate::leanh::lean_box(0);
                            v_isShared_3486_ = v_isSharedCheck_3490_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            14 => {
                return v___x_3408_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v_a_3411_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3415_ = crate::leanh::lean_ctor_get(v_a_3411_, 0);
                    crate::leanh::lean_inc(v_val_3415_);
                    crate::leanh::lean_dec_ref_known(v_a_3411_, 1);
                    v___x_3416_ = (crate::leanh::lean_unbox(v_val_3415_) as u16);
                    crate::leanh::lean_dec(v_val_3415_);
                    v___x_3417_ = lean_uint16_to_nat(v___x_3416_);
                    v_r_3418_ = l_Lean_mkRawNatLit(v___x_3417_);
                    v___x_3419_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8_once),
                        _init_l_Lean_Meta_normLitValue___closed__8,
                    );
                    v___x_3420_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__21),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__21_once),
                        _init_l_Lean_Meta_normLitValue___closed__21,
                    );
                    v___x_3421_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__23),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__23_once),
                        _init_l_Lean_Meta_normLitValue___closed__23,
                    );
                    crate::leanh::lean_inc_ref(v_r_3418_);
                    v___x_3422_ = l_Lean_Expr_app___override(v___x_3421_, v_r_3418_);
                    v___x_3423_ = l_Lean_mkApp3(v___x_3419_, v___x_3420_, v_r_3418_, v___x_3422_);
                    if v_isShared_3414_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3413_, 0, v___x_3423_);
                        v___x_3425_ = v___x_3413_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3426_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
                        v___x_3425_ = v_reuseFailAlloc_3426_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3413_);
                    crate::leanh::lean_dec(v_a_3411_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3427_ = l_Lean_Meta_getUInt32Value_x3f(
                        v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3427_) == 0 {
                        v_a_3428_ = crate::leanh::lean_ctor_get(v___x_3427_, 0);
                        v_isSharedCheck_3473_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3427_)) as u8;
                        if v_isSharedCheck_3473_ == 0 {
                            v___x_3430_ = v___x_3427_;
                            v_isShared_3431_ = v_isSharedCheck_3473_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3428_);
                            crate::leanh::lean_dec(v___x_3427_);
                            v___x_3430_ = crate::leanh::lean_box(0);
                            v_isShared_3431_ = v_isSharedCheck_3473_;
                            state = 17;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_a_3474_ = crate::leanh::lean_ctor_get(v___x_3427_, 0);
                        v_isSharedCheck_3481_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3427_)) as u8;
                        if v_isSharedCheck_3481_ == 0 {
                            v___x_3476_ = v___x_3427_;
                            v_isShared_3477_ = v_isSharedCheck_3481_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3474_);
                            crate::leanh::lean_dec(v___x_3427_);
                            v___x_3476_ = crate::leanh::lean_box(0);
                            v_isShared_3477_ = v_isSharedCheck_3481_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            16 => {
                return v___x_3425_;
            }
            17 => {
                if crate::leanh::lean_obj_tag(v_a_3428_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3432_ = crate::leanh::lean_ctor_get(v_a_3428_, 0);
                    crate::leanh::lean_inc(v_val_3432_);
                    crate::leanh::lean_dec_ref_known(v_a_3428_, 1);
                    v___x_3433_ = crate::leanh::lean_unbox_uint32(v_val_3432_);
                    crate::leanh::lean_dec(v_val_3432_);
                    v___x_3434_ = lean_uint32_to_nat(v___x_3433_);
                    v_r_3435_ = l_Lean_mkRawNatLit(v___x_3434_);
                    v___x_3436_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8_once),
                        _init_l_Lean_Meta_normLitValue___closed__8,
                    );
                    v___x_3437_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__24),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__24_once),
                        _init_l_Lean_Meta_normLitValue___closed__24,
                    );
                    v___x_3438_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__26),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__26_once),
                        _init_l_Lean_Meta_normLitValue___closed__26,
                    );
                    crate::leanh::lean_inc_ref(v_r_3435_);
                    v___x_3439_ = l_Lean_Expr_app___override(v___x_3438_, v_r_3435_);
                    v___x_3440_ = l_Lean_mkApp3(v___x_3436_, v___x_3437_, v_r_3435_, v___x_3439_);
                    if v_isShared_3431_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3430_, 0, v___x_3440_);
                        v___x_3442_ = v___x_3430_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
                        v___x_3442_ = v_reuseFailAlloc_3443_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3430_);
                    crate::leanh::lean_dec(v_a_3428_);
                    crate::leanh::lean_inc(v_a_3300_);
                    v___x_3444_ = l_Lean_Meta_getUInt64Value_x3f(
                        v_a_3300_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3444_) == 0 {
                        v_a_3445_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                        v_isSharedCheck_3464_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3444_)) as u8;
                        if v_isSharedCheck_3464_ == 0 {
                            v___x_3447_ = v___x_3444_;
                            v_isShared_3448_ = v_isSharedCheck_3464_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3445_);
                            crate::leanh::lean_dec(v___x_3444_);
                            v___x_3447_ = crate::leanh::lean_box(0);
                            v_isShared_3448_ = v_isSharedCheck_3464_;
                            state = 19;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3300_);
                        v_a_3465_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                        v_isSharedCheck_3472_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3444_)) as u8;
                        if v_isSharedCheck_3472_ == 0 {
                            v___x_3467_ = v___x_3444_;
                            v_isShared_3468_ = v_isSharedCheck_3472_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3465_);
                            crate::leanh::lean_dec(v___x_3444_);
                            v___x_3467_ = crate::leanh::lean_box(0);
                            v_isShared_3468_ = v_isSharedCheck_3472_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            18 => {
                return v___x_3442_;
            }
            19 => {
                if crate::leanh::lean_obj_tag(v_a_3445_) == 1 {
                    crate::leanh::lean_dec(v_a_3300_);
                    v_val_3449_ = crate::leanh::lean_ctor_get(v_a_3445_, 0);
                    crate::leanh::lean_inc(v_val_3449_);
                    crate::leanh::lean_dec_ref_known(v_a_3445_, 1);
                    v___x_3450_ = crate::leanh::lean_unbox_uint64(v_val_3449_);
                    crate::leanh::lean_dec(v_val_3449_);
                    v___x_3451_ = lean_uint64_to_nat(v___x_3450_);
                    v_r_3452_ = l_Lean_mkRawNatLit(v___x_3451_);
                    v___x_3453_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__8_once),
                        _init_l_Lean_Meta_normLitValue___closed__8,
                    );
                    v___x_3454_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__27),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__27_once),
                        _init_l_Lean_Meta_normLitValue___closed__27,
                    );
                    v___x_3455_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__29),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__29_once),
                        _init_l_Lean_Meta_normLitValue___closed__29,
                    );
                    crate::leanh::lean_inc_ref(v_r_3452_);
                    v___x_3456_ = l_Lean_Expr_app___override(v___x_3455_, v_r_3452_);
                    v___x_3457_ = l_Lean_mkApp3(v___x_3453_, v___x_3454_, v_r_3452_, v___x_3456_);
                    if v_isShared_3448_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3447_, 0, v___x_3457_);
                        v___x_3459_ = v___x_3447_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
                        v___x_3459_ = v_reuseFailAlloc_3460_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3445_);
                    if v_isShared_3448_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3447_, 0, v_a_3300_);
                        v___x_3462_ = v___x_3447_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3300_);
                        v___x_3462_ = v_reuseFailAlloc_3463_;
                        state = 21;
                        continue;
                    }
                }
            }
            20 => {
                return v___x_3459_;
            }
            21 => {
                return v___x_3462_;
            }
            22 => {
                if v_isShared_3468_ == 0 {
                    v___x_3470_ = v___x_3467_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3471_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
                    v___x_3470_ = v_reuseFailAlloc_3471_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3470_;
            }
            24 => {
                if v_isShared_3477_ == 0 {
                    v___x_3479_ = v___x_3476_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
                    v___x_3479_ = v_reuseFailAlloc_3480_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3479_;
            }
            26 => {
                if v_isShared_3486_ == 0 {
                    v___x_3488_ = v___x_3485_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
                    v___x_3488_ = v_reuseFailAlloc_3489_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3488_;
            }
            28 => {
                if v_isShared_3495_ == 0 {
                    v___x_3497_ = v___x_3494_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
                    v___x_3497_ = v_reuseFailAlloc_3498_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3497_;
            }
            30 => {
                if v_isShared_3504_ == 0 {
                    v___x_3506_ = v___x_3503_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
                    v___x_3506_ = v_reuseFailAlloc_3507_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3506_;
            }
            32 => {
                if v_isShared_3513_ == 0 {
                    v___x_3515_ = v___x_3512_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
                    v___x_3515_ = v_reuseFailAlloc_3516_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3515_;
            }
            34 => {
                if v_isShared_3522_ == 0 {
                    v___x_3524_ = v___x_3521_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
                    v___x_3524_ = v_reuseFailAlloc_3525_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3524_;
            }
            36 => {
                if v_isShared_3531_ == 0 {
                    v___x_3533_ = v___x_3530_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
                    v___x_3533_ = v_reuseFailAlloc_3534_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3533_;
            }
            38 => {
                if v_isShared_3540_ == 0 {
                    v___x_3542_ = v___x_3539_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3543_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
                    v___x_3542_ = v_reuseFailAlloc_3543_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_normLitValue___boxed(
    mut v_e_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3551_ = l_Lean_Meta_normLitValue(v_e_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
    crate::leanh::lean_dec(v_a_3549_);
    crate::leanh::lean_dec_ref(v_a_3548_);
    crate::leanh::lean_dec(v_a_3547_);
    crate::leanh::lean_dec_ref(v_a_3546_);
    return v_res_3551_;
}
pub unsafe fn l_Lean_Meta_isLitValue(
    mut v_e_3552_: *mut crate::leanh::LeanObject,
    mut v_a_3553_: *mut crate::leanh::LeanObject,
    mut v_a_3554_: *mut crate::leanh::LeanObject,
    mut v_a_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3569_: u8 = 0;
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3580_: u8 = 0;
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3586_: u8 = 0;
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3596_: u8 = 0;
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3606_: u8 = 0;
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3616_: u8 = 0;
    let mut v_a_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3629_: u8 = 0;
    let mut v_a_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3633_: u8 = 0;
    let mut v___x_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3637_: u8 = 0;
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3642_: u8 = 0;
    let mut v_a_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3646_: u8 = 0;
    let mut v___x_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut v_a_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3668_: u8 = 0;
    let mut v_a_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3676_: u8 = 0;
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_a_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_a_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut v_a_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3715_: u8 = 0;
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3719_: u8 = 0;
    let mut v___x_3720_: u8 = 0;
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3725_: u8 = 0;
    let mut v_a_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3558_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
                        v_e_3552_, v_a_3554_,
                    );
                v_a_3559_ = crate::leanh::lean_ctor_get(v___x_3558_, 0);
                crate::leanh::lean_inc(v_a_3559_);
                crate::leanh::lean_dec_ref(v___x_3558_);
                v___x_3560_ = l_Lean_Meta_getNatValue_x3f(
                    v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                );
                if crate::leanh::lean_obj_tag(v___x_3560_) == 0 {
                    v_a_3561_ = crate::leanh::lean_ctor_get(v___x_3560_, 0);
                    v_isSharedCheck_3725_ = (!crate::leanh::lean_is_exclusive(v___x_3560_)) as u8;
                    if v_isSharedCheck_3725_ == 0 {
                        v___x_3563_ = v___x_3560_;
                        v_isShared_3564_ = v_isSharedCheck_3725_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3561_);
                        crate::leanh::lean_dec(v___x_3560_);
                        v___x_3563_ = crate::leanh::lean_box(0);
                        v_isShared_3564_ = v_isSharedCheck_3725_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3559_);
                    v_a_3726_ = crate::leanh::lean_ctor_get(v___x_3560_, 0);
                    v_isSharedCheck_3733_ = (!crate::leanh::lean_is_exclusive(v___x_3560_)) as u8;
                    if v_isSharedCheck_3733_ == 0 {
                        v___x_3728_ = v___x_3560_;
                        v_isShared_3729_ = v_isSharedCheck_3733_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3726_);
                        crate::leanh::lean_dec(v___x_3560_);
                        v___x_3728_ = crate::leanh::lean_box(0);
                        v_isShared_3729_ = v_isSharedCheck_3733_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3561_) == 0 {
                    crate::leanh::lean_del_object(v___x_3563_);
                    crate::leanh::lean_inc(v_a_3559_);
                    v___x_3565_ = l_Lean_Meta_getIntValue_x3f(
                        v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3565_) == 0 {
                        v_a_3566_ = crate::leanh::lean_ctor_get(v___x_3565_, 0);
                        v_isSharedCheck_3711_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3565_)) as u8;
                        if v_isSharedCheck_3711_ == 0 {
                            v___x_3568_ = v___x_3565_;
                            v_isShared_3569_ = v_isSharedCheck_3711_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3566_);
                            crate::leanh::lean_dec(v___x_3565_);
                            v___x_3568_ = crate::leanh::lean_box(0);
                            v_isShared_3569_ = v_isSharedCheck_3711_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3559_);
                        v_a_3712_ = crate::leanh::lean_ctor_get(v___x_3565_, 0);
                        v_isSharedCheck_3719_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3565_)) as u8;
                        if v_isSharedCheck_3719_ == 0 {
                            v___x_3714_ = v___x_3565_;
                            v_isShared_3715_ = v_isSharedCheck_3719_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3712_);
                            crate::leanh::lean_dec(v___x_3565_);
                            v___x_3714_ = crate::leanh::lean_box(0);
                            v_isShared_3715_ = v_isSharedCheck_3719_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3561_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3720_ = 1;
                    v___x_3721_ = crate::leanh::lean_box((v___x_3720_) as usize);
                    if v_isShared_3564_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3563_, 0, v___x_3721_);
                        v___x_3723_ = v___x_3563_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_3724_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
                        v___x_3723_ = v_reuseFailAlloc_3724_;
                        state = 36;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3570_ = 1;
                if crate::leanh::lean_obj_tag(v_a_3566_) == 0 {
                    crate::leanh::lean_del_object(v___x_3568_);
                    crate::leanh::lean_inc(v_a_3559_);
                    v___x_3571_ = l_Lean_Meta_getFinValue_x3f(
                        v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3571_) == 0 {
                        v_a_3572_ = crate::leanh::lean_ctor_get(v___x_3571_, 0);
                        v_isSharedCheck_3698_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3571_)) as u8;
                        if v_isSharedCheck_3698_ == 0 {
                            v___x_3574_ = v___x_3571_;
                            v_isShared_3575_ = v_isSharedCheck_3698_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3572_);
                            crate::leanh::lean_dec(v___x_3571_);
                            v___x_3574_ = crate::leanh::lean_box(0);
                            v_isShared_3575_ = v_isSharedCheck_3698_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3559_);
                        v_a_3699_ = crate::leanh::lean_ctor_get(v___x_3571_, 0);
                        v_isSharedCheck_3706_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3571_)) as u8;
                        if v_isSharedCheck_3706_ == 0 {
                            v___x_3701_ = v___x_3571_;
                            v_isShared_3702_ = v_isSharedCheck_3706_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3699_);
                            crate::leanh::lean_dec(v___x_3571_);
                            v___x_3701_ = crate::leanh::lean_box(0);
                            v_isShared_3702_ = v_isSharedCheck_3706_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3566_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3707_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3569_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3568_, 0, v___x_3707_);
                        v___x_3709_ = v___x_3568_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_3710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
                        v___x_3709_ = v_reuseFailAlloc_3710_;
                        state = 33;
                        continue;
                    }
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_3572_) == 0 {
                    crate::leanh::lean_del_object(v___x_3574_);
                    crate::leanh::lean_inc(v_a_3559_);
                    v___x_3576_ = l_Lean_Meta_getBitVecValue_x3f(
                        v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3576_) == 0 {
                        v_a_3577_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                        v_isSharedCheck_3685_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3576_)) as u8;
                        if v_isSharedCheck_3685_ == 0 {
                            v___x_3579_ = v___x_3576_;
                            v_isShared_3580_ = v_isSharedCheck_3685_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3577_);
                            crate::leanh::lean_dec(v___x_3576_);
                            v___x_3579_ = crate::leanh::lean_box(0);
                            v_isShared_3580_ = v_isSharedCheck_3685_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3559_);
                        v_a_3686_ = crate::leanh::lean_ctor_get(v___x_3576_, 0);
                        v_isSharedCheck_3693_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3576_)) as u8;
                        if v_isSharedCheck_3693_ == 0 {
                            v___x_3688_ = v___x_3576_;
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3686_);
                            crate::leanh::lean_dec(v___x_3576_);
                            v___x_3688_ = crate::leanh::lean_box(0);
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 28;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3572_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3694_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3575_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3694_);
                        v___x_3696_ = v___x_3574_;
                        state = 30;
                        continue;
                    } else {
                        v_reuseFailAlloc_3697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3694_);
                        v___x_3696_ = v_reuseFailAlloc_3697_;
                        state = 30;
                        continue;
                    }
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_3577_) == 0 {
                    crate::leanh::lean_inc(v_a_3559_);
                    v___x_3581_ = l_Lean_Meta_getStringValue_x3f(v_a_3559_);
                    if crate::leanh::lean_obj_tag(v___x_3581_) == 0 {
                        crate::leanh::lean_del_object(v___x_3579_);
                        crate::leanh::lean_inc(v_a_3559_);
                        v___x_3582_ = l_Lean_Meta_getCharValue_x3f(
                            v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3582_) == 0 {
                            v_a_3583_ = crate::leanh::lean_ctor_get(v___x_3582_, 0);
                            v_isSharedCheck_3668_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3582_)) as u8;
                            if v_isSharedCheck_3668_ == 0 {
                                v___x_3585_ = v___x_3582_;
                                v_isShared_3586_ = v_isSharedCheck_3668_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3583_);
                                crate::leanh::lean_dec(v___x_3582_);
                                v___x_3585_ = crate::leanh::lean_box(0);
                                v_isShared_3586_ = v_isSharedCheck_3668_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3559_);
                            v_a_3669_ = crate::leanh::lean_ctor_get(v___x_3582_, 0);
                            v_isSharedCheck_3676_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3582_)) as u8;
                            if v_isSharedCheck_3676_ == 0 {
                                v___x_3671_ = v___x_3582_;
                                v_isShared_3672_ = v_isSharedCheck_3676_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3669_);
                                crate::leanh::lean_dec(v___x_3582_);
                                v___x_3671_ = crate::leanh::lean_box(0);
                                v_isShared_3672_ = v_isSharedCheck_3676_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_3581_, 1);
                        crate::leanh::lean_dec(v_a_3559_);
                        v___x_3677_ = crate::leanh::lean_box((v___x_3570_) as usize);
                        if v_isShared_3580_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3677_);
                            v___x_3679_ = v___x_3579_;
                            state = 26;
                            continue;
                        } else {
                            v_reuseFailAlloc_3680_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3677_);
                            v___x_3679_ = v_reuseFailAlloc_3680_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3577_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3681_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3580_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3681_);
                        v___x_3683_ = v___x_3579_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
                        v___x_3683_ = v_reuseFailAlloc_3684_;
                        state = 27;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_3583_) == 0 {
                    crate::leanh::lean_del_object(v___x_3585_);
                    crate::leanh::lean_inc(v_a_3559_);
                    v___x_3587_ = l_Lean_Meta_getUInt8Value_x3f(
                        v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3587_) == 0 {
                        v_a_3588_ = crate::leanh::lean_ctor_get(v___x_3587_, 0);
                        v_isSharedCheck_3655_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3587_)) as u8;
                        if v_isSharedCheck_3655_ == 0 {
                            v___x_3590_ = v___x_3587_;
                            v_isShared_3591_ = v_isSharedCheck_3655_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3588_);
                            crate::leanh::lean_dec(v___x_3587_);
                            v___x_3590_ = crate::leanh::lean_box(0);
                            v_isShared_3591_ = v_isSharedCheck_3655_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3559_);
                        v_a_3656_ = crate::leanh::lean_ctor_get(v___x_3587_, 0);
                        v_isSharedCheck_3663_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3587_)) as u8;
                        if v_isSharedCheck_3663_ == 0 {
                            v___x_3658_ = v___x_3587_;
                            v_isShared_3659_ = v_isSharedCheck_3663_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3656_);
                            crate::leanh::lean_dec(v___x_3587_);
                            v___x_3658_ = crate::leanh::lean_box(0);
                            v_isShared_3659_ = v_isSharedCheck_3663_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3583_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3664_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3586_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3585_, 0, v___x_3664_);
                        v___x_3666_ = v___x_3585_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_3667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
                        v___x_3666_ = v_reuseFailAlloc_3667_;
                        state = 23;
                        continue;
                    }
                }
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_3588_) == 0 {
                    crate::leanh::lean_del_object(v___x_3590_);
                    crate::leanh::lean_inc(v_a_3559_);
                    v___x_3592_ = l_Lean_Meta_getUInt16Value_x3f(
                        v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3592_) == 0 {
                        v_a_3593_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                        v_isSharedCheck_3642_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3592_)) as u8;
                        if v_isSharedCheck_3642_ == 0 {
                            v___x_3595_ = v___x_3592_;
                            v_isShared_3596_ = v_isSharedCheck_3642_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3593_);
                            crate::leanh::lean_dec(v___x_3592_);
                            v___x_3595_ = crate::leanh::lean_box(0);
                            v_isShared_3596_ = v_isSharedCheck_3642_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3559_);
                        v_a_3643_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                        v_isSharedCheck_3650_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3592_)) as u8;
                        if v_isSharedCheck_3650_ == 0 {
                            v___x_3645_ = v___x_3592_;
                            v_isShared_3646_ = v_isSharedCheck_3650_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3643_);
                            crate::leanh::lean_dec(v___x_3592_);
                            v___x_3645_ = crate::leanh::lean_box(0);
                            v_isShared_3646_ = v_isSharedCheck_3650_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3588_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3651_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3591_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3590_, 0, v___x_3651_);
                        v___x_3653_ = v___x_3590_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3654_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3651_);
                        v___x_3653_ = v_reuseFailAlloc_3654_;
                        state = 20;
                        continue;
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_3593_) == 0 {
                    crate::leanh::lean_del_object(v___x_3595_);
                    crate::leanh::lean_inc(v_a_3559_);
                    v___x_3597_ = l_Lean_Meta_getUInt32Value_x3f(
                        v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3597_) == 0 {
                        v_a_3598_ = crate::leanh::lean_ctor_get(v___x_3597_, 0);
                        v_isSharedCheck_3629_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3597_)) as u8;
                        if v_isSharedCheck_3629_ == 0 {
                            v___x_3600_ = v___x_3597_;
                            v_isShared_3601_ = v_isSharedCheck_3629_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3598_);
                            crate::leanh::lean_dec(v___x_3597_);
                            v___x_3600_ = crate::leanh::lean_box(0);
                            v_isShared_3601_ = v_isSharedCheck_3629_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3559_);
                        v_a_3630_ = crate::leanh::lean_ctor_get(v___x_3597_, 0);
                        v_isSharedCheck_3637_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3597_)) as u8;
                        if v_isSharedCheck_3637_ == 0 {
                            v___x_3632_ = v___x_3597_;
                            v_isShared_3633_ = v_isSharedCheck_3637_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3630_);
                            crate::leanh::lean_dec(v___x_3597_);
                            v___x_3632_ = crate::leanh::lean_box(0);
                            v_isShared_3633_ = v_isSharedCheck_3637_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3593_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3638_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3596_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3595_, 0, v___x_3638_);
                        v___x_3640_ = v___x_3595_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3641_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3641_, 0, v___x_3638_);
                        v___x_3640_ = v_reuseFailAlloc_3641_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                if crate::leanh::lean_obj_tag(v_a_3598_) == 0 {
                    crate::leanh::lean_del_object(v___x_3600_);
                    v___x_3602_ = l_Lean_Meta_getUInt64Value_x3f(
                        v_a_3559_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3602_) == 0 {
                        v_a_3603_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                        v_isSharedCheck_3616_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                        if v_isSharedCheck_3616_ == 0 {
                            v___x_3605_ = v___x_3602_;
                            v_isShared_3606_ = v_isSharedCheck_3616_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3603_);
                            crate::leanh::lean_dec(v___x_3602_);
                            v___x_3605_ = crate::leanh::lean_box(0);
                            v_isShared_3606_ = v_isSharedCheck_3616_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_3617_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                        v_isSharedCheck_3624_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                        if v_isSharedCheck_3624_ == 0 {
                            v___x_3619_ = v___x_3602_;
                            v_isShared_3620_ = v_isSharedCheck_3624_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3617_);
                            crate::leanh::lean_dec(v___x_3602_);
                            v___x_3619_ = crate::leanh::lean_box(0);
                            v_isShared_3620_ = v_isSharedCheck_3624_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3598_, 1);
                    crate::leanh::lean_dec(v_a_3559_);
                    v___x_3625_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3601_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3600_, 0, v___x_3625_);
                        v___x_3627_ = v___x_3600_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3628_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
                        v___x_3627_ = v_reuseFailAlloc_3628_;
                        state = 14;
                        continue;
                    }
                }
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_3603_) == 0 {
                    v___x_3607_ = 0;
                    v___x_3608_ = crate::leanh::lean_box((v___x_3607_) as usize);
                    if v_isShared_3606_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3605_, 0, v___x_3608_);
                        v___x_3610_ = v___x_3605_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
                        v___x_3610_ = v_reuseFailAlloc_3611_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_a_3603_, 1);
                    v___x_3612_ = crate::leanh::lean_box((v___x_3570_) as usize);
                    if v_isShared_3606_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3605_, 0, v___x_3612_);
                        v___x_3614_ = v___x_3605_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
                        v___x_3614_ = v_reuseFailAlloc_3615_;
                        state = 11;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_3610_;
            }
            11 => {
                return v___x_3614_;
            }
            12 => {
                if v_isShared_3620_ == 0 {
                    v___x_3622_ = v___x_3619_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3622_;
            }
            14 => {
                return v___x_3627_;
            }
            15 => {
                if v_isShared_3633_ == 0 {
                    v___x_3635_ = v___x_3632_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
                    v___x_3635_ = v_reuseFailAlloc_3636_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3635_;
            }
            17 => {
                return v___x_3640_;
            }
            18 => {
                if v_isShared_3646_ == 0 {
                    v___x_3648_ = v___x_3645_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3649_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
                    v___x_3648_ = v_reuseFailAlloc_3649_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3648_;
            }
            20 => {
                return v___x_3653_;
            }
            21 => {
                if v_isShared_3659_ == 0 {
                    v___x_3661_ = v___x_3658_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
                    v___x_3661_ = v_reuseFailAlloc_3662_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3661_;
            }
            23 => {
                return v___x_3666_;
            }
            24 => {
                if v_isShared_3672_ == 0 {
                    v___x_3674_ = v___x_3671_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
                    v___x_3674_ = v_reuseFailAlloc_3675_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3674_;
            }
            26 => {
                return v___x_3679_;
            }
            27 => {
                return v___x_3683_;
            }
            28 => {
                if v_isShared_3689_ == 0 {
                    v___x_3691_ = v___x_3688_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3691_;
            }
            30 => {
                return v___x_3696_;
            }
            31 => {
                if v_isShared_3702_ == 0 {
                    v___x_3704_ = v___x_3701_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3705_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
                    v___x_3704_ = v_reuseFailAlloc_3705_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3704_;
            }
            33 => {
                return v___x_3709_;
            }
            34 => {
                if v_isShared_3715_ == 0 {
                    v___x_3717_ = v___x_3714_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3718_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
                    v___x_3717_ = v_reuseFailAlloc_3718_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3717_;
            }
            36 => {
                return v___x_3723_;
            }
            37 => {
                if v_isShared_3729_ == 0 {
                    v___x_3731_ = v___x_3728_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
                    v___x_3731_ = v_reuseFailAlloc_3732_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isLitValue___boxed(
    mut v_e_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3740_ = l_Lean_Meta_isLitValue(v_e_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
    crate::leanh::lean_dec(v_a_3738_);
    crate::leanh::lean_dec_ref(v_a_3737_);
    crate::leanh::lean_dec(v_a_3736_);
    crate::leanh::lean_dec_ref(v_a_3735_);
    return v_res_3740_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3745_ = crate::leanh::lean_box(0);
    v___x_3746_ = l_Lean_Meta_litToCtor___closed__1;
    v___x_3747_ = l_Lean_mkConst(v___x_3746_, v___x_3745_);
    return v___x_3747_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3752_ = crate::leanh::lean_box(0);
    v___x_3753_ = l_Lean_Meta_litToCtor___closed__4;
    v___x_3754_ = l_Lean_mkConst(v___x_3753_, v___x_3752_);
    return v___x_3754_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = crate::leanh::lean_box(0);
    v___x_3759_ = l_Lean_Meta_litToCtor___closed__6;
    v___x_3760_ = l_Lean_mkConst(v___x_3759_, v___x_3758_);
    return v___x_3760_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3765_ = crate::leanh::lean_box(0);
    v___x_3766_ = l_Lean_Meta_litToCtor___closed__9;
    v___x_3767_ = l_Lean_mkConst(v___x_3766_, v___x_3765_);
    return v___x_3767_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3768_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3769_ = lean_nat_to_int(v___x_3768_);
    return v___x_3769_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3775_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__2_once),
        _init_l_Lean_Meta_normLitValue___closed__2,
    );
    v___x_3776_ = l_Lean_Meta_litToCtor___closed__14;
    v___x_3777_ = l_Lean_mkConst(v___x_3776_, v___x_3775_);
    return v___x_3777_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3778_ = crate::leanh::lean_box(0);
    v___x_3779_ = l_Lean_Meta_getNatValue_x3f___closed__1;
    v___x_3780_ = l_Lean_mkConst(v___x_3779_, v___x_3778_);
    return v___x_3780_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__19() -> *mut crate::leanh::LeanObject {
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3784_ = crate::leanh::lean_box(0);
    v___x_3785_ = l_Lean_Meta_litToCtor___closed__18;
    v___x_3786_ = l_Lean_mkConst(v___x_3785_, v___x_3784_);
    return v___x_3786_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__22() -> *mut crate::leanh::LeanObject {
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3790_ = crate::leanh::lean_box(0);
    v___x_3791_ = l_Lean_Meta_litToCtor___closed__21;
    v___x_3792_ = l_Lean_mkConst(v___x_3791_, v___x_3790_);
    return v___x_3792_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__25() -> *mut crate::leanh::LeanObject {
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3797_ = crate::leanh::lean_box(0);
    v___x_3798_ = l_Lean_Meta_litToCtor___closed__24;
    v___x_3799_ = l_Lean_mkConst(v___x_3798_, v___x_3797_);
    return v___x_3799_;
}
pub unsafe fn _init_l_Lean_Meta_litToCtor___closed__28() -> *mut crate::leanh::LeanObject {
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3804_ = crate::leanh::lean_box(0);
    v___x_3805_ = l_Lean_Meta_litToCtor___closed__27;
    v___x_3806_ = l_Lean_mkConst(v___x_3805_, v___x_3804_);
    return v___x_3806_;
}
pub unsafe fn l_Lean_Meta_litToCtor(
    mut v_e_3807_: *mut crate::leanh::LeanObject,
    mut v_a_3808_: *mut crate::leanh::LeanObject,
    mut v_a_3809_: *mut crate::leanh::LeanObject,
    mut v_a_3810_: *mut crate::leanh::LeanObject,
    mut v_a_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3819_: u8 = 0;
    let mut v_val_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: u8 = 0;
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v_val_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u8 = 0;
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3864_: u8 = 0;
    let mut v_val_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_a_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_a_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3904_: u8 = 0;
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_a_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3909_: u8 = 0;
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3813_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
                        v_e_3807_, v_a_3809_,
                    );
                v_a_3814_ = crate::leanh::lean_ctor_get(v___x_3813_, 0);
                crate::leanh::lean_inc(v_a_3814_);
                crate::leanh::lean_dec_ref(v___x_3813_);
                v___x_3815_ = l_Lean_Meta_getNatValue_x3f(
                    v_a_3814_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_,
                );
                if crate::leanh::lean_obj_tag(v___x_3815_) == 0 {
                    v_a_3816_ = crate::leanh::lean_ctor_get(v___x_3815_, 0);
                    v_isSharedCheck_3905_ = (!crate::leanh::lean_is_exclusive(v___x_3815_)) as u8;
                    if v_isSharedCheck_3905_ == 0 {
                        v___x_3818_ = v___x_3815_;
                        v_isShared_3819_ = v_isSharedCheck_3905_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3816_);
                        crate::leanh::lean_dec(v___x_3815_);
                        v___x_3818_ = crate::leanh::lean_box(0);
                        v_isShared_3819_ = v_isSharedCheck_3905_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3814_);
                    v_a_3906_ = crate::leanh::lean_ctor_get(v___x_3815_, 0);
                    v_isSharedCheck_3913_ = (!crate::leanh::lean_is_exclusive(v___x_3815_)) as u8;
                    if v_isSharedCheck_3913_ == 0 {
                        v___x_3908_ = v___x_3815_;
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3906_);
                        crate::leanh::lean_dec(v___x_3815_);
                        v___x_3908_ = crate::leanh::lean_box(0);
                        v_isShared_3909_ = v_isSharedCheck_3913_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3816_) == 1 {
                    crate::leanh::lean_dec(v_a_3814_);
                    v_val_3820_ = crate::leanh::lean_ctor_get(v_a_3816_, 0);
                    crate::leanh::lean_inc(v_val_3820_);
                    crate::leanh::lean_dec_ref_known(v_a_3816_, 1);
                    v___x_3821_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3822_ = lean_nat_dec_eq(v_val_3820_, v___x_3821_);
                    if v___x_3822_ == 0 {
                        v___x_3823_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__2_once),
                            _init_l_Lean_Meta_litToCtor___closed__2,
                        );
                        v___x_3824_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3825_ = lean_nat_sub(v_val_3820_, v___x_3824_);
                        crate::leanh::lean_dec(v_val_3820_);
                        v___x_3826_ = l_Lean_mkNatLit(v___x_3825_);
                        v___x_3827_ = l_Lean_Expr_app___override(v___x_3823_, v___x_3826_);
                        if v_isShared_3819_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3818_, 0, v___x_3827_);
                            v___x_3829_ = v___x_3818_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3830_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3827_);
                            v___x_3829_ = v_reuseFailAlloc_3830_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3820_);
                        v___x_3831_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__5_once),
                            _init_l_Lean_Meta_litToCtor___closed__5,
                        );
                        if v_isShared_3819_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3818_, 0, v___x_3831_);
                            v___x_3833_ = v___x_3818_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3834_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
                            v___x_3833_ = v_reuseFailAlloc_3834_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3818_);
                    crate::leanh::lean_dec(v_a_3816_);
                    crate::leanh::lean_inc(v_a_3814_);
                    v___x_3835_ = l_Lean_Meta_getIntValue_x3f(
                        v_a_3814_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3835_) == 0 {
                        v_a_3836_ = crate::leanh::lean_ctor_get(v___x_3835_, 0);
                        v_isSharedCheck_3896_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3835_)) as u8;
                        if v_isSharedCheck_3896_ == 0 {
                            v___x_3838_ = v___x_3835_;
                            v_isShared_3839_ = v_isSharedCheck_3896_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3836_);
                            crate::leanh::lean_dec(v___x_3835_);
                            v___x_3838_ = crate::leanh::lean_box(0);
                            v_isShared_3839_ = v_isSharedCheck_3896_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3814_);
                        v_a_3897_ = crate::leanh::lean_ctor_get(v___x_3835_, 0);
                        v_isSharedCheck_3904_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3835_)) as u8;
                        if v_isSharedCheck_3904_ == 0 {
                            v___x_3899_ = v___x_3835_;
                            v_isShared_3900_ = v_isSharedCheck_3904_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3897_);
                            crate::leanh::lean_dec(v___x_3835_);
                            v___x_3899_ = crate::leanh::lean_box(0);
                            v_isShared_3900_ = v_isSharedCheck_3904_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3829_;
            }
            3 => {
                return v___x_3833_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_a_3836_) == 1 {
                    crate::leanh::lean_dec(v_a_3814_);
                    v_val_3840_ = crate::leanh::lean_ctor_get(v_a_3836_, 0);
                    crate::leanh::lean_inc(v_val_3840_);
                    crate::leanh::lean_dec_ref_known(v_a_3836_, 1);
                    v___x_3841_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Meta_normLitValue___closed__0_once),
                        _init_l_Lean_Meta_normLitValue___closed__0,
                    );
                    v___x_3842_ = lean_int_dec_lt(v_val_3840_, v___x_3841_);
                    if v___x_3842_ == 0 {
                        v___x_3843_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__7),
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__7_once),
                            _init_l_Lean_Meta_litToCtor___closed__7,
                        );
                        v___x_3844_ = l_Int_toNat(v_val_3840_);
                        crate::leanh::lean_dec(v_val_3840_);
                        v___x_3845_ = l_Lean_mkNatLit(v___x_3844_);
                        v___x_3846_ = l_Lean_Expr_app___override(v___x_3843_, v___x_3845_);
                        if v_isShared_3839_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3838_, 0, v___x_3846_);
                            v___x_3848_ = v___x_3838_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3849_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3846_);
                            v___x_3848_ = v_reuseFailAlloc_3849_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___x_3850_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__10),
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__10_once),
                            _init_l_Lean_Meta_litToCtor___closed__10,
                        );
                        v___x_3851_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__11),
                            core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__11_once),
                            _init_l_Lean_Meta_litToCtor___closed__11,
                        );
                        v___x_3852_ = lean_int_add(v_val_3840_, v___x_3851_);
                        crate::leanh::lean_dec(v_val_3840_);
                        v___x_3853_ = lean_int_neg(v___x_3852_);
                        crate::leanh::lean_dec(v___x_3852_);
                        v___x_3854_ = l_Int_toNat(v___x_3853_);
                        crate::leanh::lean_dec(v___x_3853_);
                        v___x_3855_ = l_Lean_mkNatLit(v___x_3854_);
                        v___x_3856_ = l_Lean_Expr_app___override(v___x_3850_, v___x_3855_);
                        if v_isShared_3839_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3838_, 0, v___x_3856_);
                            v___x_3858_ = v___x_3838_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3859_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
                            v___x_3858_ = v_reuseFailAlloc_3859_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3838_);
                    crate::leanh::lean_dec(v_a_3836_);
                    crate::leanh::lean_inc(v_a_3814_);
                    v___x_3860_ = l_Lean_Meta_getFinValue_x3f(
                        v_a_3814_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3860_) == 0 {
                        v_a_3861_ = crate::leanh::lean_ctor_get(v___x_3860_, 0);
                        v_isSharedCheck_3887_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3860_)) as u8;
                        if v_isSharedCheck_3887_ == 0 {
                            v___x_3863_ = v___x_3860_;
                            v_isShared_3864_ = v_isSharedCheck_3887_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3861_);
                            crate::leanh::lean_dec(v___x_3860_);
                            v___x_3863_ = crate::leanh::lean_box(0);
                            v_isShared_3864_ = v_isSharedCheck_3887_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3814_);
                        v_a_3888_ = crate::leanh::lean_ctor_get(v___x_3860_, 0);
                        v_isSharedCheck_3895_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3860_)) as u8;
                        if v_isSharedCheck_3895_ == 0 {
                            v___x_3890_ = v___x_3860_;
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3888_);
                            crate::leanh::lean_dec(v___x_3860_);
                            v___x_3890_ = crate::leanh::lean_box(0);
                            v_isShared_3891_ = v_isSharedCheck_3895_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_3848_;
            }
            6 => {
                return v___x_3858_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_3861_) == 1 {
                    crate::leanh::lean_dec(v_a_3814_);
                    v_val_3865_ = crate::leanh::lean_ctor_get(v_a_3861_, 0);
                    crate::leanh::lean_inc(v_val_3865_);
                    crate::leanh::lean_dec_ref_known(v_a_3861_, 1);
                    v_fst_3866_ = crate::leanh::lean_ctor_get(v_val_3865_, 0);
                    crate::leanh::lean_inc(v_fst_3866_);
                    v_snd_3867_ = crate::leanh::lean_ctor_get(v_val_3865_, 1);
                    crate::leanh::lean_inc(v_snd_3867_);
                    crate::leanh::lean_dec(v_val_3865_);
                    v___x_3868_ = l_Lean_mkNatLit(v_snd_3867_);
                    v___x_3869_ = l_Lean_mkNatLit(v_fst_3866_);
                    v___x_3870_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__15_once),
                        _init_l_Lean_Meta_litToCtor___closed__15,
                    );
                    v___x_3871_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__16),
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__16_once),
                        _init_l_Lean_Meta_litToCtor___closed__16,
                    );
                    v___x_3872_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__19),
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__19_once),
                        _init_l_Lean_Meta_litToCtor___closed__19,
                    );
                    crate::leanh::lean_inc_ref_n(v___x_3869_, 2);
                    crate::leanh::lean_inc_ref_n(v___x_3868_, 2);
                    v___x_3873_ = l_Lean_mkApp4(
                        v___x_3870_,
                        v___x_3871_,
                        v___x_3872_,
                        v___x_3868_,
                        v___x_3869_,
                    );
                    v___x_3874_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__22),
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__22_once),
                        _init_l_Lean_Meta_litToCtor___closed__22,
                    );
                    v___x_3875_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__25),
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__25_once),
                        _init_l_Lean_Meta_litToCtor___closed__25,
                    );
                    v___x_3876_ = l_Lean_mkAppB(v___x_3875_, v___x_3868_, v___x_3869_);
                    v___x_3877_ = l_Lean_eagerReflBoolTrue;
                    v___x_3878_ = l_Lean_mkApp3(v___x_3874_, v___x_3873_, v___x_3876_, v___x_3877_);
                    v___x_3879_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__28),
                        core::ptr::addr_of_mut!(l_Lean_Meta_litToCtor___closed__28_once),
                        _init_l_Lean_Meta_litToCtor___closed__28,
                    );
                    v___x_3880_ = l_Lean_mkApp3(v___x_3879_, v___x_3869_, v___x_3868_, v___x_3878_);
                    if v_isShared_3864_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3863_, 0, v___x_3880_);
                        v___x_3882_ = v___x_3863_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3883_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
                        v___x_3882_ = v_reuseFailAlloc_3883_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3861_);
                    if v_isShared_3864_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3863_, 0, v_a_3814_);
                        v___x_3885_ = v___x_3863_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3814_);
                        v___x_3885_ = v_reuseFailAlloc_3886_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_3882_;
            }
            9 => {
                return v___x_3885_;
            }
            10 => {
                if v_isShared_3891_ == 0 {
                    v___x_3893_ = v___x_3890_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3894_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3893_;
            }
            12 => {
                if v_isShared_3900_ == 0 {
                    v___x_3902_ = v___x_3899_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3897_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3902_;
            }
            14 => {
                if v_isShared_3909_ == 0 {
                    v___x_3911_ = v___x_3908_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3912_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
                    v___x_3911_ = v_reuseFailAlloc_3912_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3911_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_litToCtor___boxed(
    mut v_e_3914_: *mut crate::leanh::LeanObject,
    mut v_a_3915_: *mut crate::leanh::LeanObject,
    mut v_a_3916_: *mut crate::leanh::LeanObject,
    mut v_a_3917_: *mut crate::leanh::LeanObject,
    mut v_a_3918_: *mut crate::leanh::LeanObject,
    mut v_a_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3920_ = l_Lean_Meta_litToCtor(v_e_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_);
    crate::leanh::lean_dec(v_a_3918_);
    crate::leanh::lean_dec_ref(v_a_3917_);
    crate::leanh::lean_dec(v_a_3916_);
    crate::leanh::lean_dec_ref(v_a_3915_);
    return v_res_3920_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(
    mut v_fst_3923_: *mut crate::leanh::LeanObject,
    mut v_snd_3924_: *mut crate::leanh::LeanObject,
    mut v_x_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3931_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___closed__0;
    v___x_3932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3932_, 0, v_fst_3923_);
    crate::leanh::lean_ctor_set(v___x_3932_, 1, v_snd_3924_);
    v___x_3933_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3933_, 0, v___x_3931_);
    crate::leanh::lean_ctor_set(v___x_3933_, 1, v___x_3932_);
    v___x_3934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3934_, 0, v___x_3933_);
    v___x_3935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3935_, 0, v___x_3934_);
    return v___x_3935_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0___boxed(
    mut v_fst_3936_: *mut crate::leanh::LeanObject,
    mut v_snd_3937_: *mut crate::leanh::LeanObject,
    mut v_x_3938_: *mut crate::leanh::LeanObject,
    mut v___y_3939_: *mut crate::leanh::LeanObject,
    mut v___y_3940_: *mut crate::leanh::LeanObject,
    mut v___y_3941_: *mut crate::leanh::LeanObject,
    mut v___y_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3944_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3936_, v_snd_3937_, v_x_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
    crate::leanh::lean_dec(v___y_3942_);
    crate::leanh::lean_dec_ref(v___y_3941_);
    crate::leanh::lean_dec(v___y_3940_);
    crate::leanh::lean_dec_ref(v___y_3939_);
    return v_res_3944_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(
    mut v_f_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v___y_3958_: *mut crate::leanh::LeanObject,
    mut v___y_3959_: *mut crate::leanh::LeanObject,
    mut v___y_3960_: *mut crate::leanh::LeanObject,
    mut v___y_3961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v_a_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut v_a_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3983_: u8 = 0;
    let mut v_snd_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v_fst_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3992_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3997_: u8 = 0;
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: u8 = 0;
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: u8 = 0;
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: u8 = 0;
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4024_: u8 = 0;
    let mut v_val_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4044_: u8 = 0;
    let mut v_a_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4052_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4062_: u8 = 0;
    let mut v_a_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4070_: u8 = 0;
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut v_unused_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3984_ = crate::leanh::lean_ctor_get(v_a_3957_, 1);
                v_isSharedCheck_4072_ = (!crate::leanh::lean_is_exclusive(v_a_3957_)) as u8;
                if v_isSharedCheck_4072_ == 0 {
                    v_unused_4073_ = crate::leanh::lean_ctor_get(v_a_3957_, 0);
                    crate::leanh::lean_dec(v_unused_4073_);
                    v___x_3986_ = v_a_3957_;
                    v_isShared_3987_ = v_isSharedCheck_4072_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3984_);
                    crate::leanh::lean_dec(v_a_3957_);
                    v___x_3986_ = crate::leanh::lean_box(0);
                    v_isShared_3987_ = v_isSharedCheck_4072_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_3964_) == 0 {
                    v_a_3965_ = crate::leanh::lean_ctor_get(v___y_3964_, 0);
                    v_isSharedCheck_3975_ = (!crate::leanh::lean_is_exclusive(v___y_3964_)) as u8;
                    if v_isSharedCheck_3975_ == 0 {
                        v___x_3967_ = v___y_3964_;
                        v_isShared_3968_ = v_isSharedCheck_3975_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3965_);
                        crate::leanh::lean_dec(v___y_3964_);
                        v___x_3967_ = crate::leanh::lean_box(0);
                        v_isShared_3968_ = v_isSharedCheck_3975_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_3956_);
                    v_a_3976_ = crate::leanh::lean_ctor_get(v___y_3964_, 0);
                    v_isSharedCheck_3983_ = (!crate::leanh::lean_is_exclusive(v___y_3964_)) as u8;
                    if v_isSharedCheck_3983_ == 0 {
                        v___x_3978_ = v___y_3964_;
                        v_isShared_3979_ = v_isSharedCheck_3983_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3976_);
                        crate::leanh::lean_dec(v___y_3964_);
                        v___x_3978_ = crate::leanh::lean_box(0);
                        v_isShared_3979_ = v_isSharedCheck_3983_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3965_) == 0 {
                    crate::leanh::lean_dec_ref(v_f_3956_);
                    v_a_3969_ = crate::leanh::lean_ctor_get(v_a_3965_, 0);
                    crate::leanh::lean_inc(v_a_3969_);
                    crate::leanh::lean_dec_ref_known(v_a_3965_, 1);
                    if v_isShared_3968_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3967_, 0, v_a_3969_);
                        v___x_3971_ = v___x_3967_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3972_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3972_, 0, v_a_3969_);
                        v___x_3971_ = v_reuseFailAlloc_3972_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3967_);
                    v_a_3973_ = crate::leanh::lean_ctor_get(v_a_3965_, 0);
                    crate::leanh::lean_inc(v_a_3973_);
                    crate::leanh::lean_dec_ref_known(v_a_3965_, 1);
                    v_a_3957_ = v_a_3973_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_3971_;
            }
            4 => {
                if v_isShared_3979_ == 0 {
                    v___x_3981_ = v___x_3978_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
                    v___x_3981_ = v_reuseFailAlloc_3982_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3981_;
            }
            6 => {
                v_fst_3988_ = crate::leanh::lean_ctor_get(v_snd_3984_, 0);
                v_snd_3989_ = crate::leanh::lean_ctor_get(v_snd_3984_, 1);
                v_isSharedCheck_4071_ = (!crate::leanh::lean_is_exclusive(v_snd_3984_)) as u8;
                if v_isSharedCheck_4071_ == 0 {
                    v___x_3991_ = v_snd_3984_;
                    v_isShared_3992_ = v_isSharedCheck_4071_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3989_);
                    crate::leanh::lean_inc(v_fst_3988_);
                    crate::leanh::lean_dec(v_snd_3984_);
                    v___x_3991_ = crate::leanh::lean_box(0);
                    v_isShared_3992_ = v_isSharedCheck_4071_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc(v_fst_3988_);
                v___x_3993_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_fst_3988_, v___y_3959_);
                if crate::leanh::lean_obj_tag(v___x_3993_) == 0 {
                    v_a_3994_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                    v_isSharedCheck_4062_ = (!crate::leanh::lean_is_exclusive(v___x_3993_)) as u8;
                    if v_isSharedCheck_4062_ == 0 {
                        v___x_3996_ = v___x_3993_;
                        v_isShared_3997_ = v_isSharedCheck_4062_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3994_);
                        crate::leanh::lean_dec(v___x_3993_);
                        v___x_3996_ = crate::leanh::lean_box(0);
                        v_isShared_3997_ = v_isSharedCheck_4062_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3991_);
                    crate::leanh::lean_dec(v_snd_3989_);
                    crate::leanh::lean_dec(v_fst_3988_);
                    crate::leanh::lean_del_object(v___x_3986_);
                    crate::leanh::lean_dec_ref(v_f_3956_);
                    v_a_4063_ = crate::leanh::lean_ctor_get(v___x_3993_, 0);
                    v_isSharedCheck_4070_ = (!crate::leanh::lean_is_exclusive(v___x_3993_)) as u8;
                    if v_isSharedCheck_4070_ == 0 {
                        v___x_4065_ = v___x_3993_;
                        v_isShared_4066_ = v_isSharedCheck_4070_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4063_);
                        crate::leanh::lean_dec(v___x_3993_);
                        v___x_4065_ = crate::leanh::lean_box(0);
                        v_isShared_4066_ = v_isSharedCheck_4070_;
                        state = 20;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3998_ = l_Lean_Expr_cleanupAnnotations(v_a_3994_);
                v___x_3999_ = l_Lean_Expr_isApp(v___x_3998_);
                if v___x_3999_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3998_);
                    crate::leanh::lean_del_object(v___x_3996_);
                    crate::leanh::lean_del_object(v___x_3991_);
                    crate::leanh::lean_del_object(v___x_3986_);
                    v___x_4000_ = crate::leanh::lean_box(0);
                    v___x_4001_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3988_, v_snd_3989_, v___x_4000_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
                    v___y_3964_ = v___x_4001_;
                    state = 1;
                    continue;
                } else {
                    v_arg_4002_ = crate::leanh::lean_ctor_get(v___x_3998_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4002_);
                    v___x_4003_ = crate::leanh::lean_box(0);
                    v___x_4004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3998_);
                    v___x_4005_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__2;
                    v___x_4006_ = l_Lean_Expr_isConstOf(v___x_4004_, v___x_4005_);
                    if v___x_4006_ == 0 {
                        crate::leanh::lean_del_object(v___x_3996_);
                        v___x_4007_ = l_Lean_Expr_isApp(v___x_4004_);
                        if v___x_4007_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4004_);
                            crate::leanh::lean_dec_ref(v_arg_4002_);
                            crate::leanh::lean_del_object(v___x_3991_);
                            crate::leanh::lean_del_object(v___x_3986_);
                            v___x_4008_ = crate::leanh::lean_box(0);
                            v___x_4009_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3988_, v_snd_3989_, v___x_4008_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
                            v___y_3964_ = v___x_4009_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_4010_ = crate::leanh::lean_ctor_get(v___x_4004_, 1);
                            crate::leanh::lean_inc_ref(v_arg_4010_);
                            v___x_4011_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4004_);
                            v___x_4012_ = l_Lean_Expr_isApp(v___x_4011_);
                            if v___x_4012_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4011_);
                                crate::leanh::lean_dec_ref(v_arg_4010_);
                                crate::leanh::lean_dec_ref(v_arg_4002_);
                                crate::leanh::lean_del_object(v___x_3991_);
                                crate::leanh::lean_del_object(v___x_3986_);
                                v___x_4013_ = crate::leanh::lean_box(0);
                                v___x_4014_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3988_, v_snd_3989_, v___x_4013_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
                                v___y_3964_ = v___x_4014_;
                                state = 1;
                                continue;
                            } else {
                                v___x_4015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4011_);
                                v___x_4016_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__4;
                                v___x_4017_ = l_Lean_Expr_isConstOf(v___x_4015_, v___x_4016_);
                                crate::leanh::lean_dec_ref(v___x_4015_);
                                if v___x_4017_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_4010_);
                                    crate::leanh::lean_dec_ref(v_arg_4002_);
                                    crate::leanh::lean_del_object(v___x_3991_);
                                    crate::leanh::lean_del_object(v___x_3986_);
                                    v___x_4018_ = crate::leanh::lean_box(0);
                                    v___x_4019_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___lam__0(v_fst_3988_, v_snd_3989_, v___x_4018_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
                                    v___y_3964_ = v___x_4019_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc_ref(v_f_3956_);
                                    crate::leanh::lean_inc(v___y_3961_);
                                    crate::leanh::lean_inc_ref(v___y_3960_);
                                    crate::leanh::lean_inc(v___y_3959_);
                                    crate::leanh::lean_inc_ref(v___y_3958_);
                                    v___x_4020_ = crate::leanh::lean_apply_6(
                                        v_f_3956_,
                                        v_arg_4010_,
                                        v___y_3958_,
                                        v___y_3959_,
                                        v___y_3960_,
                                        v___y_3961_,
                                        crate::leanh::lean_box(0),
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4020_) == 0 {
                                        v_a_4021_ = crate::leanh::lean_ctor_get(v___x_4020_, 0);
                                        v_isSharedCheck_4044_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4020_)) as u8;
                                        if v_isSharedCheck_4044_ == 0 {
                                            v___x_4023_ = v___x_4020_;
                                            v_isShared_4024_ = v_isSharedCheck_4044_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4021_);
                                            crate::leanh::lean_dec(v___x_4020_);
                                            v___x_4023_ = crate::leanh::lean_box(0);
                                            v_isShared_4024_ = v_isSharedCheck_4044_;
                                            state = 9;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_4002_);
                                        crate::leanh::lean_del_object(v___x_3991_);
                                        crate::leanh::lean_dec(v_snd_3989_);
                                        crate::leanh::lean_dec(v_fst_3988_);
                                        crate::leanh::lean_del_object(v___x_3986_);
                                        crate::leanh::lean_dec_ref(v_f_3956_);
                                        v_a_4045_ = crate::leanh::lean_ctor_get(v___x_4020_, 0);
                                        v_isSharedCheck_4052_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4020_)) as u8;
                                        if v_isSharedCheck_4052_ == 0 {
                                            v___x_4047_ = v___x_4020_;
                                            v_isShared_4048_ = v_isSharedCheck_4052_;
                                            state = 15;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4045_);
                                            crate::leanh::lean_dec(v___x_4020_);
                                            v___x_4047_ = crate::leanh::lean_box(0);
                                            v_isShared_4048_ = v_isSharedCheck_4052_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4004_);
                        crate::leanh::lean_dec_ref(v_arg_4002_);
                        crate::leanh::lean_dec_ref(v_f_3956_);
                        if v_isShared_3992_ == 0 {
                            v___x_4054_ = v___x_3991_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_4061_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_fst_3988_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_snd_3989_);
                            v___x_4054_ = v_reuseFailAlloc_4061_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_4021_) == 1 {
                    crate::leanh::lean_del_object(v___x_4023_);
                    crate::leanh::lean_dec(v_fst_3988_);
                    v_val_4025_ = crate::leanh::lean_ctor_get(v_a_4021_, 0);
                    crate::leanh::lean_inc(v_val_4025_);
                    crate::leanh::lean_dec_ref_known(v_a_4021_, 1);
                    v___x_4026_ = lean_array_push(v_snd_3989_, v_val_4025_);
                    if v_isShared_3992_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3991_, 1, v___x_4026_);
                        crate::leanh::lean_ctor_set(v___x_3991_, 0, v_arg_4002_);
                        v___x_4028_ = v___x_3991_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_arg_4002_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4033_, 1, v___x_4026_);
                        v___x_4028_ = v_reuseFailAlloc_4033_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4021_);
                    crate::leanh::lean_dec_ref(v_arg_4002_);
                    crate::leanh::lean_dec_ref(v_f_3956_);
                    v___x_4034_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___closed__5;
                    if v_isShared_3992_ == 0 {
                        v___x_4036_ = v___x_3991_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_fst_3988_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 1, v_snd_3989_);
                        v___x_4036_ = v_reuseFailAlloc_4043_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_3987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3986_, 1, v___x_4028_);
                    crate::leanh::lean_ctor_set(v___x_3986_, 0, v___x_4003_);
                    v___x_4030_ = v___x_3986_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4032_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4032_, 1, v___x_4028_);
                    v___x_4030_ = v_reuseFailAlloc_4032_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_3957_ = v___x_4030_;
                state = 0;
                continue;
            }
            12 => {
                if v_isShared_3987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3986_, 1, v___x_4036_);
                    crate::leanh::lean_ctor_set(v___x_3986_, 0, v___x_4034_);
                    v___x_4038_ = v___x_3986_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4042_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 0, v___x_4034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 1, v___x_4036_);
                    v___x_4038_ = v_reuseFailAlloc_4042_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4024_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4023_, 0, v___x_4038_);
                    v___x_4040_ = v___x_4023_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4041_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
                    v___x_4040_ = v_reuseFailAlloc_4041_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4040_;
            }
            15 => {
                if v_isShared_4048_ == 0 {
                    v___x_4050_ = v___x_4047_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
                    v___x_4050_ = v_reuseFailAlloc_4051_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4050_;
            }
            17 => {
                if v_isShared_3987_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3986_, 1, v___x_4054_);
                    crate::leanh::lean_ctor_set(v___x_3986_, 0, v___x_4003_);
                    v___x_4056_ = v___x_3986_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4054_);
                    v___x_4056_ = v_reuseFailAlloc_4060_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3997_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3996_, 0, v___x_4056_);
                    v___x_4058_ = v___x_3996_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4056_);
                    v___x_4058_ = v_reuseFailAlloc_4059_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4058_;
            }
            20 => {
                if v_isShared_4066_ == 0 {
                    v___x_4068_ = v___x_4065_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
                    v___x_4068_ = v_reuseFailAlloc_4069_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg___boxed(
    mut v_f_4074_: *mut crate::leanh::LeanObject,
    mut v_a_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
    mut v___y_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4081_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_4074_, v_a_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
    crate::leanh::lean_dec(v___y_4079_);
    crate::leanh::lean_dec_ref(v___y_4078_);
    crate::leanh::lean_dec(v___y_4077_);
    crate::leanh::lean_dec_ref(v___y_4076_);
    return v_res_4081_;
}
pub unsafe fn l_Lean_Meta_getListLitOf_x3f___redArg(
    mut v_e_4084_: *mut crate::leanh::LeanObject,
    mut v_f_4085_: *mut crate::leanh::LeanObject,
    mut v_a_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
    mut v_a_4089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4105_: u8 = 0;
    let mut v_fst_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4119_: u8 = 0;
    let mut v_a_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4123_: u8 = 0;
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4127_: u8 = 0;
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4091_ = l_Lean_Expr_consumeMData(v_e_4084_);
                v___x_4092_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
                        v___x_4091_,
                        v_a_4087_,
                    );
                v_a_4093_ = crate::leanh::lean_ctor_get(v___x_4092_, 0);
                v_isSharedCheck_4128_ = (!crate::leanh::lean_is_exclusive(v___x_4092_)) as u8;
                if v_isSharedCheck_4128_ == 0 {
                    v___x_4095_ = v___x_4092_;
                    v_isShared_4096_ = v_isSharedCheck_4128_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4093_);
                    crate::leanh::lean_dec(v___x_4092_);
                    v___x_4095_ = crate::leanh::lean_box(0);
                    v_isShared_4096_ = v_isSharedCheck_4128_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4097_ = l_Lean_Meta_getListLitOf_x3f___redArg___closed__0;
                v___x_4098_ = crate::leanh::lean_box(0);
                v___x_4099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4099_, 0, v_a_4093_);
                crate::leanh::lean_ctor_set(v___x_4099_, 1, v___x_4097_);
                v___x_4100_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4100_, 0, v___x_4098_);
                crate::leanh::lean_ctor_set(v___x_4100_, 1, v___x_4099_);
                v___x_4101_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_4085_, v___x_4100_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_);
                if crate::leanh::lean_obj_tag(v___x_4101_) == 0 {
                    v_a_4102_ = crate::leanh::lean_ctor_get(v___x_4101_, 0);
                    v_isSharedCheck_4119_ = (!crate::leanh::lean_is_exclusive(v___x_4101_)) as u8;
                    if v_isSharedCheck_4119_ == 0 {
                        v___x_4104_ = v___x_4101_;
                        v_isShared_4105_ = v_isSharedCheck_4119_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4102_);
                        crate::leanh::lean_dec(v___x_4101_);
                        v___x_4104_ = crate::leanh::lean_box(0);
                        v_isShared_4105_ = v_isSharedCheck_4119_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4095_);
                    v_a_4120_ = crate::leanh::lean_ctor_get(v___x_4101_, 0);
                    v_isSharedCheck_4127_ = (!crate::leanh::lean_is_exclusive(v___x_4101_)) as u8;
                    if v_isSharedCheck_4127_ == 0 {
                        v___x_4122_ = v___x_4101_;
                        v_isShared_4123_ = v_isSharedCheck_4127_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4120_);
                        crate::leanh::lean_dec(v___x_4101_);
                        v___x_4122_ = crate::leanh::lean_box(0);
                        v_isShared_4123_ = v_isSharedCheck_4127_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_4106_ = crate::leanh::lean_ctor_get(v_a_4102_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4106_) == 0 {
                    v_snd_4107_ = crate::leanh::lean_ctor_get(v_a_4102_, 1);
                    crate::leanh::lean_inc(v_snd_4107_);
                    crate::leanh::lean_dec(v_a_4102_);
                    v_snd_4108_ = crate::leanh::lean_ctor_get(v_snd_4107_, 1);
                    crate::leanh::lean_inc(v_snd_4108_);
                    crate::leanh::lean_dec(v_snd_4107_);
                    if v_isShared_4096_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4095_, 1);
                        crate::leanh::lean_ctor_set(v___x_4095_, 0, v_snd_4108_);
                        v___x_4110_ = v___x_4095_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_snd_4108_);
                        v___x_4110_ = v_reuseFailAlloc_4114_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4106_);
                    crate::leanh::lean_dec(v_a_4102_);
                    crate::leanh::lean_del_object(v___x_4095_);
                    v_val_4115_ = crate::leanh::lean_ctor_get(v_fst_4106_, 0);
                    crate::leanh::lean_inc(v_val_4115_);
                    crate::leanh::lean_dec_ref_known(v_fst_4106_, 1);
                    if v_isShared_4105_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4104_, 0, v_val_4115_);
                        v___x_4117_ = v___x_4104_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4118_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_val_4115_);
                        v___x_4117_ = v_reuseFailAlloc_4118_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4104_, 0, v___x_4110_);
                    v___x_4112_ = v___x_4104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4113_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4110_);
                    v___x_4112_ = v_reuseFailAlloc_4113_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4112_;
            }
            5 => {
                return v___x_4117_;
            }
            6 => {
                if v_isShared_4123_ == 0 {
                    v___x_4125_ = v___x_4122_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
                    v___x_4125_ = v_reuseFailAlloc_4126_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getListLitOf_x3f___redArg___boxed(
    mut v_e_4129_: *mut crate::leanh::LeanObject,
    mut v_f_4130_: *mut crate::leanh::LeanObject,
    mut v_a_4131_: *mut crate::leanh::LeanObject,
    mut v_a_4132_: *mut crate::leanh::LeanObject,
    mut v_a_4133_: *mut crate::leanh::LeanObject,
    mut v_a_4134_: *mut crate::leanh::LeanObject,
    mut v_a_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Lean_Meta_getListLitOf_x3f___redArg(
        v_e_4129_, v_f_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_,
    );
    crate::leanh::lean_dec(v_a_4134_);
    crate::leanh::lean_dec_ref(v_a_4133_);
    crate::leanh::lean_dec(v_a_4132_);
    crate::leanh::lean_dec_ref(v_a_4131_);
    crate::leanh::lean_dec_ref(v_e_4129_);
    return v_res_4136_;
}
pub unsafe fn l_Lean_Meta_getListLitOf_x3f(
    mut v_00_u03b1_4137_: *mut crate::leanh::LeanObject,
    mut v_e_4138_: *mut crate::leanh::LeanObject,
    mut v_f_4139_: *mut crate::leanh::LeanObject,
    mut v_a_4140_: *mut crate::leanh::LeanObject,
    mut v_a_4141_: *mut crate::leanh::LeanObject,
    mut v_a_4142_: *mut crate::leanh::LeanObject,
    mut v_a_4143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4145_ = l_Lean_Meta_getListLitOf_x3f___redArg(
        v_e_4138_, v_f_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_,
    );
    return v___x_4145_;
}
pub unsafe fn l_Lean_Meta_getListLitOf_x3f___boxed(
    mut v_00_u03b1_4146_: *mut crate::leanh::LeanObject,
    mut v_e_4147_: *mut crate::leanh::LeanObject,
    mut v_f_4148_: *mut crate::leanh::LeanObject,
    mut v_a_4149_: *mut crate::leanh::LeanObject,
    mut v_a_4150_: *mut crate::leanh::LeanObject,
    mut v_a_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4154_ = l_Lean_Meta_getListLitOf_x3f(
        v_00_u03b1_4146_,
        v_e_4147_,
        v_f_4148_,
        v_a_4149_,
        v_a_4150_,
        v_a_4151_,
        v_a_4152_,
    );
    crate::leanh::lean_dec(v_a_4152_);
    crate::leanh::lean_dec_ref(v_a_4151_);
    crate::leanh::lean_dec(v_a_4150_);
    crate::leanh::lean_dec_ref(v_a_4149_);
    crate::leanh::lean_dec_ref(v_e_4147_);
    return v_res_4154_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(
    mut v_00_u03b1_4155_: *mut crate::leanh::LeanObject,
    mut v_f_4156_: *mut crate::leanh::LeanObject,
    mut v_inst_4157_: *mut crate::leanh::LeanObject,
    mut v_a_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4164_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___redArg(v_f_4156_, v_a_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
    return v___x_4164_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0___boxed(
    mut v_00_u03b1_4165_: *mut crate::leanh::LeanObject,
    mut v_f_4166_: *mut crate::leanh::LeanObject,
    mut v_inst_4167_: *mut crate::leanh::LeanObject,
    mut v_a_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4174_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_getListLitOf_x3f_spec__0(
            v_00_u03b1_4165_,
            v_f_4166_,
            v_inst_4167_,
            v_a_4168_,
            v___y_4169_,
            v___y_4170_,
            v___y_4171_,
            v___y_4172_,
        );
    crate::leanh::lean_dec(v___y_4172_);
    crate::leanh::lean_dec_ref(v___y_4171_);
    crate::leanh::lean_dec(v___y_4170_);
    crate::leanh::lean_dec_ref(v___y_4169_);
    return v_res_4174_;
}
pub unsafe fn l_Lean_Meta_getListLit_x3f___lam__0(
    mut v_s_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4181_, 0, v_s_4175_);
    v___x_4182_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4182_, 0, v___x_4181_);
    return v___x_4182_;
}
pub unsafe fn l_Lean_Meta_getListLit_x3f___lam__0___boxed(
    mut v_s_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4189_ = l_Lean_Meta_getListLit_x3f___lam__0(
        v_s_4183_,
        v___y_4184_,
        v___y_4185_,
        v___y_4186_,
        v___y_4187_,
    );
    crate::leanh::lean_dec(v___y_4187_);
    crate::leanh::lean_dec_ref(v___y_4186_);
    crate::leanh::lean_dec(v___y_4185_);
    crate::leanh::lean_dec_ref(v___y_4184_);
    return v_res_4189_;
}
pub unsafe fn l_Lean_Meta_getListLit_x3f(
    mut v_e_4191_: *mut crate::leanh::LeanObject,
    mut v_a_4192_: *mut crate::leanh::LeanObject,
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
    mut v_a_4195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4197_ = l_Lean_Meta_getListLit_x3f___closed__0;
    v___x_4198_ = l_Lean_Meta_getListLitOf_x3f___redArg(
        v_e_4191_,
        v___f_4197_,
        v_a_4192_,
        v_a_4193_,
        v_a_4194_,
        v_a_4195_,
    );
    return v___x_4198_;
}
pub unsafe fn l_Lean_Meta_getListLit_x3f___boxed(
    mut v_e_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4205_ = l_Lean_Meta_getListLit_x3f(v_e_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_);
    crate::leanh::lean_dec(v_a_4203_);
    crate::leanh::lean_dec_ref(v_a_4202_);
    crate::leanh::lean_dec(v_a_4201_);
    crate::leanh::lean_dec_ref(v_a_4200_);
    crate::leanh::lean_dec_ref(v_e_4199_);
    return v_res_4205_;
}
pub unsafe fn l_Lean_Meta_getArrayLitOf_x3f___redArg(
    mut v_e_4210_: *mut crate::leanh::LeanObject,
    mut v_f_4211_: *mut crate::leanh::LeanObject,
    mut v_a_4212_: *mut crate::leanh::LeanObject,
    mut v_a_4213_: *mut crate::leanh::LeanObject,
    mut v_a_4214_: *mut crate::leanh::LeanObject,
    mut v_a_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: u8 = 0;
    let mut v_arg_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: u8 = 0;
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4239_: u8 = 0;
    let mut v_a_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4217_ = l_Lean_Expr_consumeMData(v_e_4210_);
                v___x_4218_ =
                    l_Lean_instantiateMVars___at___00Lean_Meta_normLitValue_spec__0___redArg(
                        v___x_4217_,
                        v_a_4213_,
                    );
                v_a_4219_ = crate::leanh::lean_ctor_get(v___x_4218_, 0);
                crate::leanh::lean_inc(v_a_4219_);
                crate::leanh::lean_dec_ref(v___x_4218_);
                v___x_4220_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_4219_, v_a_4213_);
                if crate::leanh::lean_obj_tag(v___x_4220_) == 0 {
                    v_a_4221_ = crate::leanh::lean_ctor_get(v___x_4220_, 0);
                    v_isSharedCheck_4239_ = (!crate::leanh::lean_is_exclusive(v___x_4220_)) as u8;
                    if v_isSharedCheck_4239_ == 0 {
                        v___x_4223_ = v___x_4220_;
                        v_isShared_4224_ = v_isSharedCheck_4239_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4221_);
                        crate::leanh::lean_dec(v___x_4220_);
                        v___x_4223_ = crate::leanh::lean_box(0);
                        v_isShared_4224_ = v_isSharedCheck_4239_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_4211_);
                    v_a_4240_ = crate::leanh::lean_ctor_get(v___x_4220_, 0);
                    v_isSharedCheck_4247_ = (!crate::leanh::lean_is_exclusive(v___x_4220_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v___x_4242_ = v___x_4220_;
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4240_);
                        crate::leanh::lean_dec(v___x_4220_);
                        v___x_4242_ = crate::leanh::lean_box(0);
                        v_isShared_4243_ = v_isSharedCheck_4247_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4230_ = l_Lean_Expr_cleanupAnnotations(v_a_4221_);
                v___x_4231_ = l_Lean_Expr_isApp(v___x_4230_);
                if v___x_4231_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4230_);
                    crate::leanh::lean_dec_ref(v_f_4211_);
                    state = 2;
                    continue;
                } else {
                    v_arg_4232_ = crate::leanh::lean_ctor_get(v___x_4230_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4232_);
                    v___x_4233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4230_);
                    v___x_4234_ = l_Lean_Expr_isApp(v___x_4233_);
                    if v___x_4234_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4233_);
                        crate::leanh::lean_dec_ref(v_arg_4232_);
                        crate::leanh::lean_dec_ref(v_f_4211_);
                        state = 2;
                        continue;
                    } else {
                        v___x_4235_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4233_);
                        v___x_4236_ = l_Lean_Meta_getArrayLitOf_x3f___redArg___closed__1;
                        v___x_4237_ = l_Lean_Expr_isConstOf(v___x_4235_, v___x_4236_);
                        crate::leanh::lean_dec_ref(v___x_4235_);
                        if v___x_4237_ == 0 {
                            crate::leanh::lean_dec_ref(v_arg_4232_);
                            crate::leanh::lean_dec_ref(v_f_4211_);
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_4223_);
                            v___x_4238_ = l_Lean_Meta_getListLitOf_x3f___redArg(
                                v_arg_4232_,
                                v_f_4211_,
                                v_a_4212_,
                                v_a_4213_,
                                v_a_4214_,
                                v_a_4215_,
                            );
                            crate::leanh::lean_dec_ref(v_arg_4232_);
                            return v___x_4238_;
                        }
                    }
                }
            }
            2 => {
                v___x_4226_ = crate::leanh::lean_box(0);
                if v_isShared_4224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4223_, 0, v___x_4226_);
                    v___x_4228_ = v___x_4223_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4226_);
                    v___x_4228_ = v_reuseFailAlloc_4229_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4228_;
            }
            4 => {
                if v_isShared_4243_ == 0 {
                    v___x_4245_ = v___x_4242_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
                    v___x_4245_ = v_reuseFailAlloc_4246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getArrayLitOf_x3f___redArg___boxed(
    mut v_e_4248_: *mut crate::leanh::LeanObject,
    mut v_f_4249_: *mut crate::leanh::LeanObject,
    mut v_a_4250_: *mut crate::leanh::LeanObject,
    mut v_a_4251_: *mut crate::leanh::LeanObject,
    mut v_a_4252_: *mut crate::leanh::LeanObject,
    mut v_a_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4255_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(
        v_e_4248_, v_f_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_,
    );
    crate::leanh::lean_dec(v_a_4253_);
    crate::leanh::lean_dec_ref(v_a_4252_);
    crate::leanh::lean_dec(v_a_4251_);
    crate::leanh::lean_dec_ref(v_a_4250_);
    crate::leanh::lean_dec_ref(v_e_4248_);
    return v_res_4255_;
}
pub unsafe fn l_Lean_Meta_getArrayLitOf_x3f(
    mut v_00_u03b1_4256_: *mut crate::leanh::LeanObject,
    mut v_e_4257_: *mut crate::leanh::LeanObject,
    mut v_f_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_a_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4264_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(
        v_e_4257_, v_f_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_,
    );
    return v___x_4264_;
}
pub unsafe fn l_Lean_Meta_getArrayLitOf_x3f___boxed(
    mut v_00_u03b1_4265_: *mut crate::leanh::LeanObject,
    mut v_e_4266_: *mut crate::leanh::LeanObject,
    mut v_f_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
    mut v_a_4270_: *mut crate::leanh::LeanObject,
    mut v_a_4271_: *mut crate::leanh::LeanObject,
    mut v_a_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4273_ = l_Lean_Meta_getArrayLitOf_x3f(
        v_00_u03b1_4265_,
        v_e_4266_,
        v_f_4267_,
        v_a_4268_,
        v_a_4269_,
        v_a_4270_,
        v_a_4271_,
    );
    crate::leanh::lean_dec(v_a_4271_);
    crate::leanh::lean_dec_ref(v_a_4270_);
    crate::leanh::lean_dec(v_a_4269_);
    crate::leanh::lean_dec_ref(v_a_4268_);
    crate::leanh::lean_dec_ref(v_e_4266_);
    return v_res_4273_;
}
pub unsafe fn l_Lean_Meta_getArrayLit_x3f(
    mut v_e_4274_: *mut crate::leanh::LeanObject,
    mut v_a_4275_: *mut crate::leanh::LeanObject,
    mut v_a_4276_: *mut crate::leanh::LeanObject,
    mut v_a_4277_: *mut crate::leanh::LeanObject,
    mut v_a_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4280_ = l_Lean_Meta_getListLit_x3f___closed__0;
    v___x_4281_ = l_Lean_Meta_getArrayLitOf_x3f___redArg(
        v_e_4274_,
        v___f_4280_,
        v_a_4275_,
        v_a_4276_,
        v_a_4277_,
        v_a_4278_,
    );
    return v___x_4281_;
}
pub unsafe fn l_Lean_Meta_getArrayLit_x3f___boxed(
    mut v_e_4282_: *mut crate::leanh::LeanObject,
    mut v_a_4283_: *mut crate::leanh::LeanObject,
    mut v_a_4284_: *mut crate::leanh::LeanObject,
    mut v_a_4285_: *mut crate::leanh::LeanObject,
    mut v_a_4286_: *mut crate::leanh::LeanObject,
    mut v_a_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4288_ =
        l_Lean_Meta_getArrayLit_x3f(v_e_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
    crate::leanh::lean_dec(v_a_4286_);
    crate::leanh::lean_dec_ref(v_a_4285_);
    crate::leanh::lean_dec(v_a_4284_);
    crate::leanh::lean_dec_ref(v_a_4283_);
    crate::leanh::lean_dec_ref(v_e_4282_);
    return v_res_4288_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_LitValues(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_LitValues(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_LitValues(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_While(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_LitValues(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_LitValues(builtin);
}
