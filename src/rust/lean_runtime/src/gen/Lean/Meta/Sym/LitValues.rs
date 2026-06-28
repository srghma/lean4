// Lean compiler output
// Module: Lean.Meta.Sym.LitValues
// Imports: Lean.Expr Init.Data.Rat
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_div, l_Rat_ofInt};
use crate::r#gen::Init::Data::Rat::{initialize_Init_Data_Rat, runtime_initialize_Init_Data_Rat};
use crate::r#gen::Init::Prelude::{
    l_BitVec_ofNat, l_Char_ofNat, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
};
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint32, lean_box_uint64,
    lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Sym_getNatValue_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Sym_getNatValue_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value)
                as *mut LeanObject,
            17636616155771105671 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value) as *mut LeanObject,
        15578568367168711682 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_getNatValue_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value: LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_getIntValue_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value: LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Meta_Sym_getIntValue_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value) as *mut LeanObject,
        17185717442815859305 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_getIntValue_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value: LeanStringObject<5> =
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
        m_data: [72, 68, 105, 118, 0],
    };
static mut l_Lean_Meta_Sym_getRatValue_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value: LeanStringObject<5> =
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
        m_data: [104, 68, 105, 118, 0],
    };
static mut l_Lean_Meta_Sym_getRatValue_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value)
                as *mut LeanObject,
            11858238400308895562 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value) as *mut LeanObject,
        6100819061652633370 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_getRatValue_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value: LeanStringObject<7> =
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
        m_data: [66, 105, 116, 86, 101, 99, 0],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value)
                as *mut LeanObject,
            5394957827732845164 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value)
                as *mut LeanObject,
            7578295756008745317 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value: LeanStringObject<8> =
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
        m_data: [111, 102, 78, 97, 116, 76, 84, 0],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value) as *mut LeanObject;
static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value)
                as *mut LeanObject,
            5394957827732845164 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value)
                as *mut LeanObject,
            2059920148364733515 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value)
                as *mut LeanObject,
            5394957827732845164 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value: LeanStringObject<4> =
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
        m_data: [70, 105, 110, 0],
    };
static mut l_Lean_Meta_Sym_getFinValue_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value) as *mut LeanObject,
        15815496672699636542 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_getFinValue_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value: LeanStringObject<5> =
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
        m_data: [67, 104, 97, 114, 0],
    };
static mut l_Lean_Meta_Sym_getCharValue_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value)
                as *mut LeanObject,
            14164462494711235346 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value) as *mut LeanObject,
        18098914779984442139 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Sym_getCharValue_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Sym_getNatValue_x3f(mut v_e_396_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: u8 = 0;
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: u8 = 0;
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: u8 = 0;
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: u8 = 0;
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_419_: u8 = 0;
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_397_ = l_Lean_Expr_cleanupAnnotations(v_e_396_);
                v___x_398_ = l_Lean_Expr_isApp(v___x_397_);
                if v___x_398_ == 0 {
                    lean_dec_ref(v___x_397_);
                    v___x_399_ = lean_box(0);
                    return v___x_399_;
                } else {
                    v___x_400_ = l_Lean_Expr_appFnCleanup___redArg(v___x_397_);
                    v___x_401_ = l_Lean_Expr_isApp(v___x_400_);
                    if v___x_401_ == 0 {
                        lean_dec_ref(v___x_400_);
                        v___x_402_ = lean_box(0);
                        return v___x_402_;
                    } else {
                        v_arg_403_ = lean_ctor_get(v___x_400_, 1);
                        lean_inc_ref(v_arg_403_);
                        v___x_404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
                        v___x_405_ = l_Lean_Expr_isApp(v___x_404_);
                        if v___x_405_ == 0 {
                            lean_dec_ref(v___x_404_);
                            lean_dec_ref(v_arg_403_);
                            v___x_406_ = lean_box(0);
                            return v___x_406_;
                        } else {
                            v___x_407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_404_);
                            v___x_408_ = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
                            v___x_409_ = l_Lean_Expr_isConstOf(v___x_407_, v___x_408_);
                            lean_dec_ref(v___x_407_);
                            if v___x_409_ == 0 {
                                lean_dec_ref(v_arg_403_);
                                v___x_410_ = lean_box(0);
                                return v___x_410_;
                            } else {
                                if lean_obj_tag(v_arg_403_) == 9 {
                                    v_a_411_ = lean_ctor_get(v_arg_403_, 0);
                                    lean_inc_ref(v_a_411_);
                                    lean_dec_ref_known(v_arg_403_, 1);
                                    if lean_obj_tag(v_a_411_) == 0 {
                                        v_val_412_ = lean_ctor_get(v_a_411_, 0);
                                        v_isSharedCheck_419_ = (!lean_is_exclusive(v_a_411_)) as u8;
                                        if v_isSharedCheck_419_ == 0 {
                                            v___x_414_ = v_a_411_;
                                            v_isShared_415_ = v_isSharedCheck_419_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_val_412_);
                                            lean_dec(v_a_411_);
                                            v___x_414_ = lean_box(0);
                                            v_isShared_415_ = v_isSharedCheck_419_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_a_411_);
                                        v___x_420_ = lean_box(0);
                                        return v___x_420_;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_403_);
                                    v___x_421_ = lean_box(0);
                                    return v___x_421_;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_415_ == 0 {
                    lean_ctor_set_tag(v___x_414_, 1);
                    v___x_417_ = v___x_414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_418_, 0, v_val_412_);
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
    mut v_a_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = lean_nat_to_int(v_a_422_);
    return v___x_423_;
}
pub unsafe fn l_Lean_Meta_Sym_getIntValue_x3f(mut v_e_429_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_436_: u8 = 0;
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_441_: u8 = 0;
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    let mut v_arg_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u8 = 0;
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_448_: u8 = 0;
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_457_: u8 = 0;
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_429_);
                v___x_442_ = l_Lean_Expr_cleanupAnnotations(v_e_429_);
                v___x_443_ = l_Lean_Expr_isApp(v___x_442_);
                if v___x_443_ == 0 {
                    lean_dec_ref(v___x_442_);
                    state = 1;
                    continue;
                } else {
                    v_arg_444_ = lean_ctor_get(v___x_442_, 1);
                    lean_inc_ref(v_arg_444_);
                    v___x_445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_442_);
                    v___x_446_ = l_Lean_Expr_isApp(v___x_445_);
                    if v___x_446_ == 0 {
                        lean_dec_ref(v___x_445_);
                        lean_dec_ref(v_arg_444_);
                        state = 1;
                        continue;
                    } else {
                        v___x_447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_445_);
                        v___x_448_ = l_Lean_Expr_isApp(v___x_447_);
                        if v___x_448_ == 0 {
                            lean_dec_ref(v___x_447_);
                            lean_dec_ref(v_arg_444_);
                            state = 1;
                            continue;
                        } else {
                            v___x_449_ = l_Lean_Expr_appFnCleanup___redArg(v___x_447_);
                            v___x_450_ = l_Lean_Meta_Sym_getIntValue_x3f___closed__2;
                            v___x_451_ = l_Lean_Expr_isConstOf(v___x_449_, v___x_450_);
                            lean_dec_ref(v___x_449_);
                            if v___x_451_ == 0 {
                                lean_dec_ref(v_arg_444_);
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_e_429_);
                                v___x_452_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_444_);
                                if lean_obj_tag(v___x_452_) == 0 {
                                    v___x_453_ = lean_box(0);
                                    return v___x_453_;
                                } else {
                                    v_val_454_ = lean_ctor_get(v___x_452_, 0);
                                    v_isSharedCheck_463_ = (!lean_is_exclusive(v___x_452_)) as u8;
                                    if v_isSharedCheck_463_ == 0 {
                                        v___x_456_ = v___x_452_;
                                        v_isShared_457_ = v_isSharedCheck_463_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_val_454_);
                                        lean_dec(v___x_452_);
                                        v___x_456_ = lean_box(0);
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
                if lean_obj_tag(v___x_431_) == 0 {
                    v___x_432_ = lean_box(0);
                    return v___x_432_;
                } else {
                    v_val_433_ = lean_ctor_get(v___x_431_, 0);
                    v_isSharedCheck_441_ = (!lean_is_exclusive(v___x_431_)) as u8;
                    if v_isSharedCheck_441_ == 0 {
                        v___x_435_ = v___x_431_;
                        v_isShared_436_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_433_);
                        lean_dec(v___x_431_);
                        v___x_435_ = lean_box(0);
                        v_isShared_436_ = v_isSharedCheck_441_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_437_ = lean_nat_to_int(v_val_433_);
                if v_isShared_436_ == 0 {
                    lean_ctor_set(v___x_435_, 0, v___x_437_);
                    v___x_439_ = v___x_435_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
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
                lean_dec(v___x_458_);
                if v_isShared_457_ == 0 {
                    lean_ctor_set(v___x_456_, 0, v___x_459_);
                    v___x_461_ = v___x_456_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
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
    mut v_a_464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    v___x_465_ = l_Rat_ofInt(v_a_464_);
    return v___x_465_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(
    mut v_a_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    v___x_467_ = lean_nat_to_int(v_a_466_);
    v___x_468_ = l_Rat_ofInt(v___x_467_);
    return v___x_468_;
}
pub unsafe fn l_Lean_Meta_Sym_getRatValue_x3f(mut v_e_474_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_481_: u8 = 0;
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: u8 = 0;
    let mut v_arg_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: u8 = 0;
    let mut v_arg_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: u8 = 0;
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: u8 = 0;
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: u8 = 0;
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u8 = 0;
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_512_: u8 = 0;
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_519_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_474_);
                v___x_487_ = l_Lean_Expr_cleanupAnnotations(v_e_474_);
                v___x_488_ = l_Lean_Expr_isApp(v___x_487_);
                if v___x_488_ == 0 {
                    lean_dec_ref(v___x_487_);
                    state = 1;
                    continue;
                } else {
                    v_arg_489_ = lean_ctor_get(v___x_487_, 1);
                    lean_inc_ref(v_arg_489_);
                    v___x_490_ = l_Lean_Expr_appFnCleanup___redArg(v___x_487_);
                    v___x_491_ = l_Lean_Expr_isApp(v___x_490_);
                    if v___x_491_ == 0 {
                        lean_dec_ref(v___x_490_);
                        lean_dec_ref(v_arg_489_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_492_ = lean_ctor_get(v___x_490_, 1);
                        lean_inc_ref(v_arg_492_);
                        v___x_493_ = l_Lean_Expr_appFnCleanup___redArg(v___x_490_);
                        v___x_494_ = l_Lean_Expr_isApp(v___x_493_);
                        if v___x_494_ == 0 {
                            lean_dec_ref(v___x_493_);
                            lean_dec_ref(v_arg_492_);
                            lean_dec_ref(v_arg_489_);
                            state = 1;
                            continue;
                        } else {
                            v___x_495_ = l_Lean_Expr_appFnCleanup___redArg(v___x_493_);
                            v___x_496_ = l_Lean_Expr_isApp(v___x_495_);
                            if v___x_496_ == 0 {
                                lean_dec_ref(v___x_495_);
                                lean_dec_ref(v_arg_492_);
                                lean_dec_ref(v_arg_489_);
                                state = 1;
                                continue;
                            } else {
                                v___x_497_ = l_Lean_Expr_appFnCleanup___redArg(v___x_495_);
                                v___x_498_ = l_Lean_Expr_isApp(v___x_497_);
                                if v___x_498_ == 0 {
                                    lean_dec_ref(v___x_497_);
                                    lean_dec_ref(v_arg_492_);
                                    lean_dec_ref(v_arg_489_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_497_);
                                    v___x_500_ = l_Lean_Expr_isApp(v___x_499_);
                                    if v___x_500_ == 0 {
                                        lean_dec_ref(v___x_499_);
                                        lean_dec_ref(v_arg_492_);
                                        lean_dec_ref(v_arg_489_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_499_);
                                        v___x_502_ = l_Lean_Meta_Sym_getRatValue_x3f___closed__2;
                                        v___x_503_ = l_Lean_Expr_isConstOf(v___x_501_, v___x_502_);
                                        lean_dec_ref(v___x_501_);
                                        if v___x_503_ == 0 {
                                            lean_dec_ref(v_arg_492_);
                                            lean_dec_ref(v_arg_489_);
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v_e_474_);
                                            v___x_504_ =
                                                l_Lean_Meta_Sym_getIntValue_x3f(v_arg_492_);
                                            if lean_obj_tag(v___x_504_) == 0 {
                                                lean_dec_ref(v_arg_489_);
                                                v___x_505_ = lean_box(0);
                                                return v___x_505_;
                                            } else {
                                                v_val_506_ = lean_ctor_get(v___x_504_, 0);
                                                lean_inc(v_val_506_);
                                                lean_dec_ref_known(v___x_504_, 1);
                                                v___x_507_ =
                                                    l_Lean_Meta_Sym_getNatValue_x3f(v_arg_489_);
                                                if lean_obj_tag(v___x_507_) == 0 {
                                                    lean_dec(v_val_506_);
                                                    v___x_508_ = lean_box(0);
                                                    return v___x_508_;
                                                } else {
                                                    v_val_509_ = lean_ctor_get(v___x_507_, 0);
                                                    v_isSharedCheck_519_ =
                                                        (!lean_is_exclusive(v___x_507_)) as u8;
                                                    if v_isSharedCheck_519_ == 0 {
                                                        v___x_511_ = v___x_507_;
                                                        v_isShared_512_ = v_isSharedCheck_519_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_val_509_);
                                                        lean_dec(v___x_507_);
                                                        v___x_511_ = lean_box(0);
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
                if lean_obj_tag(v___x_476_) == 0 {
                    v___x_477_ = lean_box(0);
                    return v___x_477_;
                } else {
                    v_val_478_ = lean_ctor_get(v___x_476_, 0);
                    v_isSharedCheck_486_ = (!lean_is_exclusive(v___x_476_)) as u8;
                    if v_isSharedCheck_486_ == 0 {
                        v___x_480_ = v___x_476_;
                        v_isShared_481_ = v_isSharedCheck_486_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_478_);
                        lean_dec(v___x_476_);
                        v___x_480_ = lean_box(0);
                        v_isShared_481_ = v_isSharedCheck_486_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_482_ = l_Rat_ofInt(v_val_478_);
                if v_isShared_481_ == 0 {
                    lean_ctor_set(v___x_480_, 0, v___x_482_);
                    v___x_484_ = v___x_480_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_485_, 0, v___x_482_);
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
                lean_dec_ref(v___x_513_);
                if v_isShared_512_ == 0 {
                    lean_ctor_set(v___x_511_, 0, v___x_515_);
                    v___x_517_ = v___x_511_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
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
pub unsafe fn l_Lean_Meta_Sym_getBitVecValue_x3f(mut v_e_530_: *mut LeanObject) -> *mut LeanObject {
    let mut v_nExpr_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vExpr_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_542_: u8 = 0;
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_548_: u8 = 0;
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: u8 = 0;
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: u8 = 0;
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: u8 = 0;
    let mut v___x_560_: u8 = 0;
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: u8 = 0;
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: u8 = 0;
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_583_: u8 = 0;
    let mut v_val_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_549_ = l_Lean_Expr_cleanupAnnotations(v_e_530_);
                v___x_550_ = l_Lean_Expr_isApp(v___x_549_);
                if v___x_550_ == 0 {
                    lean_dec_ref(v___x_549_);
                    v___x_551_ = lean_box(0);
                    return v___x_551_;
                } else {
                    v_arg_552_ = lean_ctor_get(v___x_549_, 1);
                    lean_inc_ref(v_arg_552_);
                    v___x_553_ = l_Lean_Expr_appFnCleanup___redArg(v___x_549_);
                    v___x_554_ = l_Lean_Expr_isApp(v___x_553_);
                    if v___x_554_ == 0 {
                        lean_dec_ref(v___x_553_);
                        lean_dec_ref(v_arg_552_);
                        v___x_555_ = lean_box(0);
                        return v___x_555_;
                    } else {
                        v_arg_556_ = lean_ctor_get(v___x_553_, 1);
                        lean_inc_ref(v_arg_556_);
                        v___x_557_ = l_Lean_Expr_appFnCleanup___redArg(v___x_553_);
                        v___x_558_ = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1;
                        v___x_559_ = l_Lean_Expr_isConstOf(v___x_557_, v___x_558_);
                        if v___x_559_ == 0 {
                            lean_dec_ref(v_arg_552_);
                            v___x_560_ = l_Lean_Expr_isApp(v___x_557_);
                            if v___x_560_ == 0 {
                                lean_dec_ref(v___x_557_);
                                lean_dec_ref(v_arg_556_);
                                v___x_561_ = lean_box(0);
                                return v___x_561_;
                            } else {
                                v_arg_562_ = lean_ctor_get(v___x_557_, 1);
                                lean_inc_ref(v_arg_562_);
                                v___x_563_ = l_Lean_Expr_appFnCleanup___redArg(v___x_557_);
                                v___x_564_ = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
                                v___x_565_ = l_Lean_Expr_isConstOf(v___x_563_, v___x_564_);
                                if v___x_565_ == 0 {
                                    v___x_566_ = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3;
                                    v___x_567_ = l_Lean_Expr_isConstOf(v___x_563_, v___x_566_);
                                    lean_dec_ref(v___x_563_);
                                    if v___x_567_ == 0 {
                                        lean_dec_ref(v_arg_562_);
                                        lean_dec_ref(v_arg_556_);
                                        v___x_568_ = lean_box(0);
                                        return v___x_568_;
                                    } else {
                                        v_nExpr_532_ = v_arg_562_;
                                        v_vExpr_533_ = v_arg_556_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v___x_563_);
                                    v___x_569_ = l_Lean_Expr_cleanupAnnotations(v_arg_562_);
                                    v___x_570_ = l_Lean_Expr_isApp(v___x_569_);
                                    if v___x_570_ == 0 {
                                        lean_dec_ref(v___x_569_);
                                        lean_dec_ref(v_arg_556_);
                                        v___x_571_ = lean_box(0);
                                        return v___x_571_;
                                    } else {
                                        v_arg_572_ = lean_ctor_get(v___x_569_, 1);
                                        lean_inc_ref(v_arg_572_);
                                        v___x_573_ = l_Lean_Expr_appFnCleanup___redArg(v___x_569_);
                                        v___x_574_ = l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4;
                                        v___x_575_ = l_Lean_Expr_isConstOf(v___x_573_, v___x_574_);
                                        lean_dec_ref(v___x_573_);
                                        if v___x_575_ == 0 {
                                            lean_dec_ref(v_arg_572_);
                                            lean_dec_ref(v_arg_556_);
                                            v___x_576_ = lean_box(0);
                                            return v___x_576_;
                                        } else {
                                            v___x_577_ =
                                                l_Lean_Meta_Sym_getNatValue_x3f(v_arg_572_);
                                            if lean_obj_tag(v___x_577_) == 0 {
                                                lean_dec_ref(v_arg_556_);
                                                v___x_578_ = lean_box(0);
                                                return v___x_578_;
                                            } else {
                                                if lean_obj_tag(v_arg_556_) == 9 {
                                                    v_a_579_ = lean_ctor_get(v_arg_556_, 0);
                                                    lean_inc_ref(v_a_579_);
                                                    lean_dec_ref_known(v_arg_556_, 1);
                                                    if lean_obj_tag(v_a_579_) == 0 {
                                                        v_val_580_ = lean_ctor_get(v___x_577_, 0);
                                                        v_isSharedCheck_590_ =
                                                            (!lean_is_exclusive(v___x_577_)) as u8;
                                                        if v_isSharedCheck_590_ == 0 {
                                                            v___x_582_ = v___x_577_;
                                                            v_isShared_583_ = v_isSharedCheck_590_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_val_580_);
                                                            lean_dec(v___x_577_);
                                                            v___x_582_ = lean_box(0);
                                                            v_isShared_583_ = v_isSharedCheck_590_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_a_579_);
                                                        lean_dec_ref_known(v___x_577_, 1);
                                                        v___x_591_ = lean_box(0);
                                                        return v___x_591_;
                                                    }
                                                } else {
                                                    lean_dec_ref_known(v___x_577_, 1);
                                                    lean_dec_ref(v_arg_556_);
                                                    v___x_592_ = lean_box(0);
                                                    return v___x_592_;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_557_);
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
                if lean_obj_tag(v___x_534_) == 0 {
                    lean_dec_ref(v_vExpr_533_);
                    v___x_535_ = lean_box(0);
                    return v___x_535_;
                } else {
                    v_val_536_ = lean_ctor_get(v___x_534_, 0);
                    lean_inc(v_val_536_);
                    lean_dec_ref_known(v___x_534_, 1);
                    v___x_537_ = l_Lean_Meta_Sym_getNatValue_x3f(v_vExpr_533_);
                    if lean_obj_tag(v___x_537_) == 0 {
                        lean_dec(v_val_536_);
                        v___x_538_ = lean_box(0);
                        return v___x_538_;
                    } else {
                        v_val_539_ = lean_ctor_get(v___x_537_, 0);
                        v_isSharedCheck_548_ = (!lean_is_exclusive(v___x_537_)) as u8;
                        if v_isSharedCheck_548_ == 0 {
                            v___x_541_ = v___x_537_;
                            v_isShared_542_ = v_isSharedCheck_548_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_539_);
                            lean_dec(v___x_537_);
                            v___x_541_ = lean_box(0);
                            v_isShared_542_ = v_isSharedCheck_548_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_543_ = l_BitVec_ofNat(v_val_536_, v_val_539_);
                lean_dec(v_val_539_);
                v___x_544_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_544_, 0, v_val_536_);
                lean_ctor_set(v___x_544_, 1, v___x_543_);
                if v_isShared_542_ == 0 {
                    lean_ctor_set(v___x_541_, 0, v___x_544_);
                    v___x_546_ = v___x_541_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
                    v___x_546_ = v_reuseFailAlloc_547_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_546_;
            }
            4 => {
                v_val_584_ = lean_ctor_get(v_a_579_, 0);
                lean_inc(v_val_584_);
                lean_dec_ref_known(v_a_579_, 1);
                v___x_585_ = l_BitVec_ofNat(v_val_580_, v_val_584_);
                lean_dec(v_val_584_);
                v___x_586_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_586_, 0, v_val_580_);
                lean_ctor_set(v___x_586_, 1, v___x_585_);
                if v_isShared_583_ == 0 {
                    lean_ctor_set(v___x_582_, 0, v___x_586_);
                    v___x_588_ = v___x_582_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
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
pub unsafe fn l_Lean_Meta_Sym_getUInt8Value_x3f(mut v_e_593_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___x_600_: u8 = 0;
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_594_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_593_);
                if lean_obj_tag(v___x_594_) == 0 {
                    v___x_595_ = lean_box(0);
                    return v___x_595_;
                } else {
                    v_val_596_ = lean_ctor_get(v___x_594_, 0);
                    v_isSharedCheck_605_ = (!lean_is_exclusive(v___x_594_)) as u8;
                    if v_isSharedCheck_605_ == 0 {
                        v___x_598_ = v___x_594_;
                        v_isShared_599_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_596_);
                        lean_dec(v___x_594_);
                        v___x_598_ = lean_box(0);
                        v_isShared_599_ = v_isSharedCheck_605_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_600_ = lean_uint8_of_nat(v_val_596_);
                lean_dec(v_val_596_);
                v___x_601_ = lean_box((v___x_600_) as usize);
                if v_isShared_599_ == 0 {
                    lean_ctor_set(v___x_598_, 0, v___x_601_);
                    v___x_603_ = v___x_598_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_601_);
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
pub unsafe fn l_Lean_Meta_Sym_getUInt16Value_x3f(mut v_e_606_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_613_: u16 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_607_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_606_);
                if lean_obj_tag(v___x_607_) == 0 {
                    v___x_608_ = lean_box(0);
                    return v___x_608_;
                } else {
                    v_val_609_ = lean_ctor_get(v___x_607_, 0);
                    v_isSharedCheck_618_ = (!lean_is_exclusive(v___x_607_)) as u8;
                    if v_isSharedCheck_618_ == 0 {
                        v___x_611_ = v___x_607_;
                        v_isShared_612_ = v_isSharedCheck_618_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_609_);
                        lean_dec(v___x_607_);
                        v___x_611_ = lean_box(0);
                        v_isShared_612_ = v_isSharedCheck_618_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_613_ = lean_uint16_of_nat(v_val_609_);
                lean_dec(v_val_609_);
                v___x_614_ = lean_box((v___x_613_) as usize);
                if v_isShared_612_ == 0 {
                    lean_ctor_set(v___x_611_, 0, v___x_614_);
                    v___x_616_ = v___x_611_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_614_);
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
pub unsafe fn l_Lean_Meta_Sym_getUInt32Value_x3f(mut v_e_619_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_625_: u8 = 0;
    let mut v___x_626_: u32 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_620_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_619_);
                if lean_obj_tag(v___x_620_) == 0 {
                    v___x_621_ = lean_box(0);
                    return v___x_621_;
                } else {
                    v_val_622_ = lean_ctor_get(v___x_620_, 0);
                    v_isSharedCheck_631_ = (!lean_is_exclusive(v___x_620_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_624_ = v___x_620_;
                        v_isShared_625_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_622_);
                        lean_dec(v___x_620_);
                        v___x_624_ = lean_box(0);
                        v_isShared_625_ = v_isSharedCheck_631_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_626_ = lean_uint32_of_nat(v_val_622_);
                lean_dec(v_val_622_);
                v___x_627_ = lean_box_uint32(v___x_626_);
                if v_isShared_625_ == 0 {
                    lean_ctor_set(v___x_624_, 0, v___x_627_);
                    v___x_629_ = v___x_624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
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
pub unsafe fn l_Lean_Meta_Sym_getUInt64Value_x3f(mut v_e_632_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_639_: u64 = 0;
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_633_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_632_);
                if lean_obj_tag(v___x_633_) == 0 {
                    v___x_634_ = lean_box(0);
                    return v___x_634_;
                } else {
                    v_val_635_ = lean_ctor_get(v___x_633_, 0);
                    v_isSharedCheck_644_ = (!lean_is_exclusive(v___x_633_)) as u8;
                    if v_isSharedCheck_644_ == 0 {
                        v___x_637_ = v___x_633_;
                        v_isShared_638_ = v_isSharedCheck_644_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_635_);
                        lean_dec(v___x_633_);
                        v___x_637_ = lean_box(0);
                        v_isShared_638_ = v_isSharedCheck_644_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_639_ = lean_uint64_of_nat(v_val_635_);
                lean_dec(v_val_635_);
                v___x_640_ = lean_box_uint64(v___x_639_);
                if v_isShared_638_ == 0 {
                    lean_ctor_set(v___x_637_, 0, v___x_640_);
                    v___x_642_ = v___x_637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
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
pub unsafe fn l_Lean_Meta_Sym_getInt8Value_x3f(mut v_e_645_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_651_: u8 = 0;
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_646_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_645_);
                if lean_obj_tag(v___x_646_) == 0 {
                    v___x_647_ = lean_box(0);
                    return v___x_647_;
                } else {
                    v_val_648_ = lean_ctor_get(v___x_646_, 0);
                    v_isSharedCheck_657_ = (!lean_is_exclusive(v___x_646_)) as u8;
                    if v_isSharedCheck_657_ == 0 {
                        v___x_650_ = v___x_646_;
                        v_isShared_651_ = v_isSharedCheck_657_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_648_);
                        lean_dec(v___x_646_);
                        v___x_650_ = lean_box(0);
                        v_isShared_651_ = v_isSharedCheck_657_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_652_ = lean_int8_of_int(v_val_648_);
                lean_dec(v_val_648_);
                v___x_653_ = lean_box((v___x_652_) as usize);
                if v_isShared_651_ == 0 {
                    lean_ctor_set(v___x_650_, 0, v___x_653_);
                    v___x_655_ = v___x_650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
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
pub unsafe fn l_Lean_Meta_Sym_getInt16Value_x3f(mut v_e_658_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_664_: u8 = 0;
    let mut v___x_665_: u16 = 0;
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_659_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_658_);
                if lean_obj_tag(v___x_659_) == 0 {
                    v___x_660_ = lean_box(0);
                    return v___x_660_;
                } else {
                    v_val_661_ = lean_ctor_get(v___x_659_, 0);
                    v_isSharedCheck_670_ = (!lean_is_exclusive(v___x_659_)) as u8;
                    if v_isSharedCheck_670_ == 0 {
                        v___x_663_ = v___x_659_;
                        v_isShared_664_ = v_isSharedCheck_670_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_661_);
                        lean_dec(v___x_659_);
                        v___x_663_ = lean_box(0);
                        v_isShared_664_ = v_isSharedCheck_670_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_665_ = lean_int16_of_int(v_val_661_);
                lean_dec(v_val_661_);
                v___x_666_ = lean_box((v___x_665_) as usize);
                if v_isShared_664_ == 0 {
                    lean_ctor_set(v___x_663_, 0, v___x_666_);
                    v___x_668_ = v___x_663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
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
pub unsafe fn l_Lean_Meta_Sym_getInt32Value_x3f(mut v_e_671_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_678_: u32 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_672_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_671_);
                if lean_obj_tag(v___x_672_) == 0 {
                    v___x_673_ = lean_box(0);
                    return v___x_673_;
                } else {
                    v_val_674_ = lean_ctor_get(v___x_672_, 0);
                    v_isSharedCheck_683_ = (!lean_is_exclusive(v___x_672_)) as u8;
                    if v_isSharedCheck_683_ == 0 {
                        v___x_676_ = v___x_672_;
                        v_isShared_677_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_674_);
                        lean_dec(v___x_672_);
                        v___x_676_ = lean_box(0);
                        v_isShared_677_ = v_isSharedCheck_683_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_678_ = lean_int32_of_int(v_val_674_);
                lean_dec(v_val_674_);
                v___x_679_ = lean_box_uint32(v___x_678_);
                if v_isShared_677_ == 0 {
                    lean_ctor_set(v___x_676_, 0, v___x_679_);
                    v___x_681_ = v___x_676_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
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
pub unsafe fn l_Lean_Meta_Sym_getInt64Value_x3f(mut v_e_684_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_691_: u64 = 0;
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_685_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_684_);
                if lean_obj_tag(v___x_685_) == 0 {
                    v___x_686_ = lean_box(0);
                    return v___x_686_;
                } else {
                    v_val_687_ = lean_ctor_get(v___x_685_, 0);
                    v_isSharedCheck_696_ = (!lean_is_exclusive(v___x_685_)) as u8;
                    if v_isSharedCheck_696_ == 0 {
                        v___x_689_ = v___x_685_;
                        v_isShared_690_ = v_isSharedCheck_696_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_687_);
                        lean_dec(v___x_685_);
                        v___x_689_ = lean_box(0);
                        v_isShared_690_ = v_isSharedCheck_696_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_691_ = lean_int64_of_int(v_val_687_);
                lean_dec(v_val_687_);
                v___x_692_ = lean_box_uint64(v___x_691_);
                if v_isShared_690_ == 0 {
                    lean_ctor_set(v___x_689_, 0, v___x_692_);
                    v___x_694_ = v___x_689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
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
pub unsafe fn l_Lean_Meta_Sym_getFinValue_x3f(mut v_e_700_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u8 = 0;
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: u8 = 0;
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u8 = 0;
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: u8 = 0;
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v_val_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_701_ = l_Lean_Expr_cleanupAnnotations(v_e_700_);
                v___x_702_ = l_Lean_Expr_isApp(v___x_701_);
                if v___x_702_ == 0 {
                    lean_dec_ref(v___x_701_);
                    v___x_703_ = lean_box(0);
                    return v___x_703_;
                } else {
                    v___x_704_ = l_Lean_Expr_appFnCleanup___redArg(v___x_701_);
                    v___x_705_ = l_Lean_Expr_isApp(v___x_704_);
                    if v___x_705_ == 0 {
                        lean_dec_ref(v___x_704_);
                        v___x_706_ = lean_box(0);
                        return v___x_706_;
                    } else {
                        v_arg_707_ = lean_ctor_get(v___x_704_, 1);
                        lean_inc_ref(v_arg_707_);
                        v___x_708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_704_);
                        v___x_709_ = l_Lean_Expr_isApp(v___x_708_);
                        if v___x_709_ == 0 {
                            lean_dec_ref(v___x_708_);
                            lean_dec_ref(v_arg_707_);
                            v___x_710_ = lean_box(0);
                            return v___x_710_;
                        } else {
                            v_arg_711_ = lean_ctor_get(v___x_708_, 1);
                            lean_inc_ref(v_arg_711_);
                            v___x_712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_708_);
                            v___x_713_ = l_Lean_Meta_Sym_getNatValue_x3f___closed__2;
                            v___x_714_ = l_Lean_Expr_isConstOf(v___x_712_, v___x_713_);
                            lean_dec_ref(v___x_712_);
                            if v___x_714_ == 0 {
                                lean_dec_ref(v_arg_711_);
                                lean_dec_ref(v_arg_707_);
                                v___x_715_ = lean_box(0);
                                return v___x_715_;
                            } else {
                                v___x_716_ = l_Lean_Expr_cleanupAnnotations(v_arg_711_);
                                v___x_717_ = l_Lean_Expr_isApp(v___x_716_);
                                if v___x_717_ == 0 {
                                    lean_dec_ref(v___x_716_);
                                    lean_dec_ref(v_arg_707_);
                                    v___x_718_ = lean_box(0);
                                    return v___x_718_;
                                } else {
                                    v_arg_719_ = lean_ctor_get(v___x_716_, 1);
                                    lean_inc_ref(v_arg_719_);
                                    v___x_720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_716_);
                                    v___x_721_ = l_Lean_Meta_Sym_getFinValue_x3f___closed__1;
                                    v___x_722_ = l_Lean_Expr_isConstOf(v___x_720_, v___x_721_);
                                    lean_dec_ref(v___x_720_);
                                    if v___x_722_ == 0 {
                                        lean_dec_ref(v_arg_719_);
                                        lean_dec_ref(v_arg_707_);
                                        v___x_723_ = lean_box(0);
                                        return v___x_723_;
                                    } else {
                                        v___x_724_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_719_);
                                        if lean_obj_tag(v___x_724_) == 0 {
                                            lean_dec_ref(v_arg_707_);
                                            v___x_725_ = lean_box(0);
                                            return v___x_725_;
                                        } else {
                                            if lean_obj_tag(v_arg_707_) == 9 {
                                                v_a_726_ = lean_ctor_get(v_arg_707_, 0);
                                                lean_inc_ref(v_a_726_);
                                                lean_dec_ref_known(v_arg_707_, 1);
                                                if lean_obj_tag(v_a_726_) == 0 {
                                                    v_val_727_ = lean_ctor_get(v___x_724_, 0);
                                                    v_isSharedCheck_740_ =
                                                        (!lean_is_exclusive(v___x_724_)) as u8;
                                                    if v_isSharedCheck_740_ == 0 {
                                                        v___x_729_ = v___x_724_;
                                                        v_isShared_730_ = v_isSharedCheck_740_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_val_727_);
                                                        lean_dec(v___x_724_);
                                                        v___x_729_ = lean_box(0);
                                                        v_isShared_730_ = v_isSharedCheck_740_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_a_726_);
                                                    lean_dec_ref_known(v___x_724_, 1);
                                                    v___x_741_ = lean_box(0);
                                                    return v___x_741_;
                                                }
                                            } else {
                                                lean_dec_ref_known(v___x_724_, 1);
                                                lean_dec_ref(v_arg_707_);
                                                v___x_742_ = lean_box(0);
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
                v_val_731_ = lean_ctor_get(v_a_726_, 0);
                lean_inc(v_val_731_);
                lean_dec_ref_known(v_a_726_, 1);
                v___x_732_ = lean_unsigned_to_nat(0);
                v___x_733_ = lean_nat_dec_eq(v_val_727_, v___x_732_);
                if v___x_733_ == 0 {
                    v___x_734_ = lean_nat_mod(v_val_731_, v_val_727_);
                    lean_dec(v_val_731_);
                    v___x_735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_735_, 0, v_val_727_);
                    lean_ctor_set(v___x_735_, 1, v___x_734_);
                    if v_isShared_730_ == 0 {
                        lean_ctor_set(v___x_729_, 0, v___x_735_);
                        v___x_737_ = v___x_729_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_735_);
                        v___x_737_ = v_reuseFailAlloc_738_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_val_731_);
                    lean_del_object(v___x_729_);
                    lean_dec(v_val_727_);
                    v___x_739_ = lean_box(0);
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
pub unsafe fn l_Lean_Meta_Sym_getCharValue_x3f(mut v_e_747_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: u8 = 0;
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_760_: u8 = 0;
    let mut v___x_761_: u32 = 0;
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_748_ = l_Lean_Expr_cleanupAnnotations(v_e_747_);
                v___x_749_ = l_Lean_Expr_isApp(v___x_748_);
                if v___x_749_ == 0 {
                    lean_dec_ref(v___x_748_);
                    v___x_750_ = lean_box(0);
                    return v___x_750_;
                } else {
                    v_arg_751_ = lean_ctor_get(v___x_748_, 1);
                    lean_inc_ref(v_arg_751_);
                    v___x_752_ = l_Lean_Expr_appFnCleanup___redArg(v___x_748_);
                    v___x_753_ = l_Lean_Meta_Sym_getCharValue_x3f___closed__1;
                    v___x_754_ = l_Lean_Expr_isConstOf(v___x_752_, v___x_753_);
                    lean_dec_ref(v___x_752_);
                    if v___x_754_ == 0 {
                        lean_dec_ref(v_arg_751_);
                        v___x_755_ = lean_box(0);
                        return v___x_755_;
                    } else {
                        if lean_obj_tag(v_arg_751_) == 9 {
                            v_a_756_ = lean_ctor_get(v_arg_751_, 0);
                            lean_inc_ref(v_a_756_);
                            lean_dec_ref_known(v_arg_751_, 1);
                            if lean_obj_tag(v_a_756_) == 0 {
                                v_val_757_ = lean_ctor_get(v_a_756_, 0);
                                v_isSharedCheck_766_ = (!lean_is_exclusive(v_a_756_)) as u8;
                                if v_isSharedCheck_766_ == 0 {
                                    v___x_759_ = v_a_756_;
                                    v_isShared_760_ = v_isSharedCheck_766_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_757_);
                                    lean_dec(v_a_756_);
                                    v___x_759_ = lean_box(0);
                                    v_isShared_760_ = v_isSharedCheck_766_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_a_756_);
                                v___x_767_ = lean_box(0);
                                return v___x_767_;
                            }
                        } else {
                            lean_dec_ref(v_arg_751_);
                            v___x_768_ = lean_box(0);
                            return v___x_768_;
                        }
                    }
                }
            }
            1 => {
                v___x_761_ = l_Char_ofNat(v_val_757_);
                lean_dec(v_val_757_);
                v___x_762_ = lean_box_uint32(v___x_761_);
                if v_isShared_760_ == 0 {
                    lean_ctor_set_tag(v___x_759_, 1);
                    lean_ctor_set(v___x_759_, 0, v___x_762_);
                    v___x_764_ = v___x_759_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
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
pub unsafe fn l_Lean_Meta_Sym_getStringValue_x3f(mut v_e_769_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_774_: u8 = 0;
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_769_) == 9 {
                    v_a_770_ = lean_ctor_get(v_e_769_, 0);
                    lean_inc_ref(v_a_770_);
                    lean_dec_ref_known(v_e_769_, 1);
                    if lean_obj_tag(v_a_770_) == 1 {
                        v_val_771_ = lean_ctor_get(v_a_770_, 0);
                        v_isSharedCheck_778_ = (!lean_is_exclusive(v_a_770_)) as u8;
                        if v_isSharedCheck_778_ == 0 {
                            v___x_773_ = v_a_770_;
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_771_);
                            lean_dec(v_a_770_);
                            v___x_773_ = lean_box(0);
                            v_isShared_774_ = v_isSharedCheck_778_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_770_);
                        v___x_779_ = lean_box(0);
                        return v___x_779_;
                    }
                } else {
                    lean_dec_ref(v_e_769_);
                    v___x_780_ = lean_box(0);
                    return v___x_780_;
                }
            }
            1 => {
                if v_isShared_774_ == 0 {
                    v___x_776_ = v___x_773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_777_, 0, v_val_771_);
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
pub unsafe fn runtime_initialize_Lean_Meta_Sym_LitValues(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_LitValues(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_LitValues(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Rat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_LitValues(builtin);
}
