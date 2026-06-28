// Lean compiler output
// Module: Lean.Meta.ProdN
// Imports: Lean.Meta.InferType Lean.Meta.DecLevel Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_constLevels_x21,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkApp4, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::{
    l_Lean_Level_normalize, l_Lean_Level_succ___override, l_Lean_mkLevelMax,
};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::DecLevel::{
    initialize_Lean_Meta_DecLevel, l_Lean_Meta_getDecLevel, runtime_initialize_Lean_Meta_DecLevel,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, runtime_initialize_Lean_Meta_InferType,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_pop;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_lt,
    lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [80, 114, 111, 100, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15289851429949568889 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkProdN___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [80, 85, 110, 105, 116, 0],
    };
static mut l_Lean_Meta_mkProdN___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProdN___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkProdN___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkProdN___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11091137386503903511 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkProdN___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProdN___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15289851429949568889 as *mut crate::leanh::LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,6466355875042130293 as *mut crate::leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_mkProdMkN___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [117, 110, 105, 116, 0],
    };
static mut l_Lean_Meta_mkProdMkN___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProdMkN___closed__0_value) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_mkProdMkN___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkProdN___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11091137386503903511 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_mkProdMkN___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_mkProdMkN___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_mkProdMkN___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14036392901208071058 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_mkProdMkN___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkProdMkN___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getProdFields___closed__0_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
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
            73, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 69, 120,
            112, 101, 99, 116, 101, 100, 32, 80, 114, 111, 100, 44, 32, 103, 111, 116, 32, 0,
        ],
    };
static mut l_Lean_Meta_getProdFields___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getProdFields___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getProdFields___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getProdFields___closed__2_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [32, 111, 102, 32, 116, 121, 112, 101, 32, 0],
    };
static mut l_Lean_Meta_getProdFields___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getProdFields___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getProdFields___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_getProdFields___closed__4_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [102, 115, 116, 0],
    };
static mut l_Lean_Meta_getProdFields___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getProdFields___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15289851429949568889 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_getProdFields___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__4_value)
                as *mut crate::leanh::LeanObject,
            8286241746160725162 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getProdFields___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_getProdFields___closed__6_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [115, 110, 100, 0],
    };
static mut l_Lean_Meta_getProdFields___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_getProdFields___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject,15289851429949568889 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_getProdFields___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__6_value)
                as *mut crate::leanh::LeanObject,
            16183457921166944291 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getProdFields___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getProdFields___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(
    mut v_upperBound_498_: *mut crate::leanh::LeanObject,
    mut v_a_499_: *mut crate::leanh::LeanObject,
    mut v_b_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
    mut v___y_502_: *mut crate::leanh::LeanObject,
    mut v___y_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_506_: u8 = 0;
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_512_: u8 = 0;
    let mut v_fst_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_517_: u8 = 0;
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_549_: u8 = 0;
    let mut v_isSharedCheck_550_: u8 = 0;
    let mut v_isSharedCheck_551_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_506_ = lean_nat_dec_lt(v_a_499_, v_upperBound_498_);
                if v___x_506_ == 0 {
                    crate::leanh::lean_dec(v_a_499_);
                    v___x_507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_507_, 0, v_b_500_);
                    return v___x_507_;
                } else {
                    v_snd_508_ = crate::leanh::lean_ctor_get(v_b_500_, 1);
                    v_fst_509_ = crate::leanh::lean_ctor_get(v_b_500_, 0);
                    v_isSharedCheck_551_ = (!crate::leanh::lean_is_exclusive(v_b_500_)) as u8;
                    if v_isSharedCheck_551_ == 0 {
                        v___x_511_ = v_b_500_;
                        v_isShared_512_ = v_isSharedCheck_551_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_508_);
                        crate::leanh::lean_inc(v_fst_509_);
                        crate::leanh::lean_dec(v_b_500_);
                        v___x_511_ = crate::leanh::lean_box(0);
                        v_isShared_512_ = v_isSharedCheck_551_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_513_ = crate::leanh::lean_ctor_get(v_snd_508_, 0);
                v_snd_514_ = crate::leanh::lean_ctor_get(v_snd_508_, 1);
                v_isSharedCheck_550_ = (!crate::leanh::lean_is_exclusive(v_snd_508_)) as u8;
                if v_isSharedCheck_550_ == 0 {
                    v___x_516_ = v_snd_508_;
                    v_isShared_517_ = v_isSharedCheck_550_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_514_);
                    crate::leanh::lean_inc(v_fst_513_);
                    crate::leanh::lean_dec(v_snd_508_);
                    v___x_516_ = crate::leanh::lean_box(0);
                    v_isShared_517_ = v_isSharedCheck_550_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_518_ = l_Lean_instInhabitedExpr;
                v___x_519_ = lean_array_get_size(v_snd_514_);
                v___x_520_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_521_ = lean_nat_sub(v___x_519_, v___x_520_);
                v___x_522_ = lean_array_get_borrowed(v___x_518_, v_snd_514_, v___x_521_);
                crate::leanh::lean_dec(v___x_521_);
                crate::leanh::lean_inc(v___x_522_);
                v___x_523_ = l_Lean_Meta_getDecLevel(
                    v___x_522_, v___y_501_, v___y_502_, v___y_503_, v___y_504_,
                );
                if crate::leanh::lean_obj_tag(v___x_523_) == 0 {
                    v_a_524_ = crate::leanh::lean_ctor_get(v___x_523_, 0);
                    crate::leanh::lean_inc_n(v_a_524_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_523_, 1);
                    v___x_525_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1;
                    v___x_526_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_fst_513_);
                    v___x_527_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_527_, 0, v_fst_513_);
                    crate::leanh::lean_ctor_set(v___x_527_, 1, v___x_526_);
                    v___x_528_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_528_, 0, v_a_524_);
                    crate::leanh::lean_ctor_set(v___x_528_, 1, v___x_527_);
                    v___x_529_ = l_Lean_mkConst(v___x_525_, v___x_528_);
                    crate::leanh::lean_inc(v___x_522_);
                    v___x_530_ = l_Lean_mkAppB(v___x_529_, v___x_522_, v_fst_509_);
                    v___x_531_ = l_Lean_mkLevelMax(v_fst_513_, v_a_524_);
                    v___x_532_ = l_Lean_Level_normalize(v___x_531_);
                    crate::leanh::lean_dec(v___x_531_);
                    v___x_533_ = lean_array_pop(v_snd_514_);
                    if v_isShared_517_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_516_, 1, v___x_533_);
                        crate::leanh::lean_ctor_set(v___x_516_, 0, v___x_532_);
                        v___x_535_ = v___x_516_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_541_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_532_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_533_);
                        v___x_535_ = v_reuseFailAlloc_541_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_516_);
                    crate::leanh::lean_dec(v_snd_514_);
                    crate::leanh::lean_dec(v_fst_513_);
                    crate::leanh::lean_del_object(v___x_511_);
                    crate::leanh::lean_dec(v_fst_509_);
                    crate::leanh::lean_dec(v_a_499_);
                    v_a_542_ = crate::leanh::lean_ctor_get(v___x_523_, 0);
                    v_isSharedCheck_549_ = (!crate::leanh::lean_is_exclusive(v___x_523_)) as u8;
                    if v_isSharedCheck_549_ == 0 {
                        v___x_544_ = v___x_523_;
                        v_isShared_545_ = v_isSharedCheck_549_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_542_);
                        crate::leanh::lean_dec(v___x_523_);
                        v___x_544_ = crate::leanh::lean_box(0);
                        v_isShared_545_ = v_isSharedCheck_549_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_512_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_511_, 1, v___x_535_);
                    crate::leanh::lean_ctor_set(v___x_511_, 0, v___x_530_);
                    v___x_537_ = v___x_511_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 1, v___x_535_);
                    v___x_537_ = v_reuseFailAlloc_540_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_538_ = lean_nat_add(v_a_499_, v___x_520_);
                crate::leanh::lean_dec(v_a_499_);
                v_a_499_ = v___x_538_;
                v_b_500_ = v___x_537_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_545_ == 0 {
                    v___x_547_ = v___x_544_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
                    v___x_547_ = v_reuseFailAlloc_548_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___boxed(
    mut v_upperBound_552_: *mut crate::leanh::LeanObject,
    mut v_a_553_: *mut crate::leanh::LeanObject,
    mut v_b_554_: *mut crate::leanh::LeanObject,
    mut v___y_555_: *mut crate::leanh::LeanObject,
    mut v___y_556_: *mut crate::leanh::LeanObject,
    mut v___y_557_: *mut crate::leanh::LeanObject,
    mut v___y_558_: *mut crate::leanh::LeanObject,
    mut v___y_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(
        v_upperBound_552_,
        v_a_553_,
        v_b_554_,
        v___y_555_,
        v___y_556_,
        v___y_557_,
        v___y_558_,
    );
    crate::leanh::lean_dec(v___y_558_);
    crate::leanh::lean_dec_ref(v___y_557_);
    crate::leanh::lean_dec(v___y_556_);
    crate::leanh::lean_dec_ref(v___y_555_);
    crate::leanh::lean_dec(v_upperBound_552_);
    return v_res_560_;
}
pub unsafe fn l_Lean_Meta_mkProdN(
    mut v_ts_564_: *mut crate::leanh::LeanObject,
    mut v_u_565_: *mut crate::leanh::LeanObject,
    mut v_a_566_: *mut crate::leanh::LeanObject,
    mut v_a_567_: *mut crate::leanh::LeanObject,
    mut v_a_568_: *mut crate::leanh::LeanObject,
    mut v_a_569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: u8 = 0;
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tupleTy_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v_fst_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v_a_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_602_: u8 = 0;
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_606_: u8 = 0;
    let mut v_a_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_571_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_572_ = lean_array_get_size(v_ts_564_);
                v___x_573_ = lean_nat_dec_lt(v___x_571_, v___x_572_);
                if v___x_573_ == 0 {
                    crate::leanh::lean_dec_ref(v_ts_564_);
                    v___x_574_ = l_Lean_Meta_mkProdN___closed__1;
                    v___x_575_ = l_Lean_Level_succ___override(v_u_565_);
                    v___x_576_ = crate::leanh::lean_box(0);
                    v___x_577_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_577_, 0, v___x_575_);
                    crate::leanh::lean_ctor_set(v___x_577_, 1, v___x_576_);
                    v___x_578_ = l_Lean_mkConst(v___x_574_, v___x_577_);
                    v___x_579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_579_, 0, v___x_578_);
                    return v___x_579_;
                } else {
                    crate::leanh::lean_dec(v_u_565_);
                    v___x_580_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_581_ = lean_nat_sub(v___x_572_, v___x_580_);
                    v_tupleTy_582_ = lean_array_fget(v_ts_564_, v___x_581_);
                    crate::leanh::lean_dec(v___x_581_);
                    crate::leanh::lean_inc(v_tupleTy_582_);
                    v___x_583_ = l_Lean_Meta_getDecLevel(
                        v_tupleTy_582_,
                        v_a_566_,
                        v_a_567_,
                        v_a_568_,
                        v_a_569_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_583_) == 0 {
                        v_a_584_ = crate::leanh::lean_ctor_get(v___x_583_, 0);
                        crate::leanh::lean_inc(v_a_584_);
                        crate::leanh::lean_dec_ref_known(v___x_583_, 1);
                        v___x_585_ = lean_array_pop(v_ts_564_);
                        v___x_586_ = lean_array_get_size(v___x_585_);
                        v___x_587_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_587_, 0, v_a_584_);
                        crate::leanh::lean_ctor_set(v___x_587_, 1, v___x_585_);
                        v___x_588_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_588_, 0, v_tupleTy_582_);
                        crate::leanh::lean_ctor_set(v___x_588_, 1, v___x_587_);
                        v___x_589_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(v___x_586_, v___x_571_, v___x_588_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
                        if crate::leanh::lean_obj_tag(v___x_589_) == 0 {
                            v_a_590_ = crate::leanh::lean_ctor_get(v___x_589_, 0);
                            v_isSharedCheck_598_ =
                                (!crate::leanh::lean_is_exclusive(v___x_589_)) as u8;
                            if v_isSharedCheck_598_ == 0 {
                                v___x_592_ = v___x_589_;
                                v_isShared_593_ = v_isSharedCheck_598_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_590_);
                                crate::leanh::lean_dec(v___x_589_);
                                v___x_592_ = crate::leanh::lean_box(0);
                                v_isShared_593_ = v_isSharedCheck_598_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_599_ = crate::leanh::lean_ctor_get(v___x_589_, 0);
                            v_isSharedCheck_606_ =
                                (!crate::leanh::lean_is_exclusive(v___x_589_)) as u8;
                            if v_isSharedCheck_606_ == 0 {
                                v___x_601_ = v___x_589_;
                                v_isShared_602_ = v_isSharedCheck_606_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_599_);
                                crate::leanh::lean_dec(v___x_589_);
                                v___x_601_ = crate::leanh::lean_box(0);
                                v_isShared_602_ = v_isSharedCheck_606_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_tupleTy_582_);
                        crate::leanh::lean_dec_ref(v_ts_564_);
                        v_a_607_ = crate::leanh::lean_ctor_get(v___x_583_, 0);
                        v_isSharedCheck_614_ = (!crate::leanh::lean_is_exclusive(v___x_583_)) as u8;
                        if v_isSharedCheck_614_ == 0 {
                            v___x_609_ = v___x_583_;
                            v_isShared_610_ = v_isSharedCheck_614_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_607_);
                            crate::leanh::lean_dec(v___x_583_);
                            v___x_609_ = crate::leanh::lean_box(0);
                            v_isShared_610_ = v_isSharedCheck_614_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_594_ = crate::leanh::lean_ctor_get(v_a_590_, 0);
                crate::leanh::lean_inc(v_fst_594_);
                crate::leanh::lean_dec(v_a_590_);
                if v_isShared_593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_592_, 0, v_fst_594_);
                    v___x_596_ = v___x_592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_597_, 0, v_fst_594_);
                    v___x_596_ = v_reuseFailAlloc_597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_596_;
            }
            3 => {
                if v_isShared_602_ == 0 {
                    v___x_604_ = v___x_601_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_605_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
                    v___x_604_ = v_reuseFailAlloc_605_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_604_;
            }
            5 => {
                if v_isShared_610_ == 0 {
                    v___x_612_ = v___x_609_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
                    v___x_612_ = v_reuseFailAlloc_613_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkProdN___boxed(
    mut v_ts_615_: *mut crate::leanh::LeanObject,
    mut v_u_616_: *mut crate::leanh::LeanObject,
    mut v_a_617_: *mut crate::leanh::LeanObject,
    mut v_a_618_: *mut crate::leanh::LeanObject,
    mut v_a_619_: *mut crate::leanh::LeanObject,
    mut v_a_620_: *mut crate::leanh::LeanObject,
    mut v_a_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Lean_Meta_mkProdN(v_ts_615_, v_u_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
    crate::leanh::lean_dec(v_a_620_);
    crate::leanh::lean_dec_ref(v_a_619_);
    crate::leanh::lean_dec(v_a_618_);
    crate::leanh::lean_dec_ref(v_a_617_);
    return v_res_622_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(
    mut v_upperBound_623_: *mut crate::leanh::LeanObject,
    mut v_inst_624_: *mut crate::leanh::LeanObject,
    mut v_R_625_: *mut crate::leanh::LeanObject,
    mut v_a_626_: *mut crate::leanh::LeanObject,
    mut v_b_627_: *mut crate::leanh::LeanObject,
    mut v_c_628_: *mut crate::leanh::LeanObject,
    mut v___y_629_: *mut crate::leanh::LeanObject,
    mut v___y_630_: *mut crate::leanh::LeanObject,
    mut v___y_631_: *mut crate::leanh::LeanObject,
    mut v___y_632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg(
        v_upperBound_623_,
        v_a_626_,
        v_b_627_,
        v___y_629_,
        v___y_630_,
        v___y_631_,
        v___y_632_,
    );
    return v___x_634_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___boxed(
    mut v_upperBound_635_: *mut crate::leanh::LeanObject,
    mut v_inst_636_: *mut crate::leanh::LeanObject,
    mut v_R_637_: *mut crate::leanh::LeanObject,
    mut v_a_638_: *mut crate::leanh::LeanObject,
    mut v_b_639_: *mut crate::leanh::LeanObject,
    mut v_c_640_: *mut crate::leanh::LeanObject,
    mut v___y_641_: *mut crate::leanh::LeanObject,
    mut v___y_642_: *mut crate::leanh::LeanObject,
    mut v___y_643_: *mut crate::leanh::LeanObject,
    mut v___y_644_: *mut crate::leanh::LeanObject,
    mut v___y_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0(
        v_upperBound_635_,
        v_inst_636_,
        v_R_637_,
        v_a_638_,
        v_b_639_,
        v_c_640_,
        v___y_641_,
        v___y_642_,
        v___y_643_,
        v___y_644_,
    );
    crate::leanh::lean_dec(v___y_644_);
    crate::leanh::lean_dec_ref(v___y_643_);
    crate::leanh::lean_dec(v___y_642_);
    crate::leanh::lean_dec_ref(v___y_641_);
    crate::leanh::lean_dec(v_upperBound_635_);
    return v_res_646_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(
    mut v_upperBound_651_: *mut crate::leanh::LeanObject,
    mut v_a_652_: *mut crate::leanh::LeanObject,
    mut v_b_653_: *mut crate::leanh::LeanObject,
    mut v___y_654_: *mut crate::leanh::LeanObject,
    mut v___y_655_: *mut crate::leanh::LeanObject,
    mut v___y_656_: *mut crate::leanh::LeanObject,
    mut v___y_657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_666_: u8 = 0;
    let mut v_fst_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v_fst_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_675_: u8 = 0;
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_715_: u8 = 0;
    let mut v_a_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_719_: u8 = 0;
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_723_: u8 = 0;
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_unused_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_727_: u8 = 0;
    let mut v_unused_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_659_ = lean_nat_dec_lt(v_a_652_, v_upperBound_651_);
                if v___x_659_ == 0 {
                    crate::leanh::lean_dec(v_a_652_);
                    v___x_660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_660_, 0, v_b_653_);
                    return v___x_660_;
                } else {
                    v_snd_661_ = crate::leanh::lean_ctor_get(v_b_653_, 1);
                    crate::leanh::lean_inc(v_snd_661_);
                    v_snd_662_ = crate::leanh::lean_ctor_get(v_snd_661_, 1);
                    crate::leanh::lean_inc(v_snd_662_);
                    v_fst_663_ = crate::leanh::lean_ctor_get(v_b_653_, 0);
                    v_isSharedCheck_727_ = (!crate::leanh::lean_is_exclusive(v_b_653_)) as u8;
                    if v_isSharedCheck_727_ == 0 {
                        v_unused_728_ = crate::leanh::lean_ctor_get(v_b_653_, 1);
                        crate::leanh::lean_dec(v_unused_728_);
                        v___x_665_ = v_b_653_;
                        v_isShared_666_ = v_isSharedCheck_727_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_663_);
                        crate::leanh::lean_dec(v_b_653_);
                        v___x_665_ = crate::leanh::lean_box(0);
                        v_isShared_666_ = v_isSharedCheck_727_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_667_ = crate::leanh::lean_ctor_get(v_snd_661_, 0);
                v_isSharedCheck_725_ = (!crate::leanh::lean_is_exclusive(v_snd_661_)) as u8;
                if v_isSharedCheck_725_ == 0 {
                    v_unused_726_ = crate::leanh::lean_ctor_get(v_snd_661_, 1);
                    crate::leanh::lean_dec(v_unused_726_);
                    v___x_669_ = v_snd_661_;
                    v_isShared_670_ = v_isSharedCheck_725_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_667_);
                    crate::leanh::lean_dec(v_snd_661_);
                    v___x_669_ = crate::leanh::lean_box(0);
                    v_isShared_670_ = v_isSharedCheck_725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_671_ = crate::leanh::lean_ctor_get(v_snd_662_, 0);
                v_snd_672_ = crate::leanh::lean_ctor_get(v_snd_662_, 1);
                v_isSharedCheck_724_ = (!crate::leanh::lean_is_exclusive(v_snd_662_)) as u8;
                if v_isSharedCheck_724_ == 0 {
                    v___x_674_ = v_snd_662_;
                    v_isShared_675_ = v_isSharedCheck_724_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_672_);
                    crate::leanh::lean_inc(v_fst_671_);
                    crate::leanh::lean_dec(v_snd_662_);
                    v___x_674_ = crate::leanh::lean_box(0);
                    v_isShared_675_ = v_isSharedCheck_724_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_676_ = l_Lean_instInhabitedExpr;
                v___x_677_ = lean_array_get_size(v_snd_672_);
                v___x_678_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_679_ = lean_nat_sub(v___x_677_, v___x_678_);
                v___x_680_ = lean_array_get_borrowed(v___x_676_, v_snd_672_, v___x_679_);
                crate::leanh::lean_dec(v___x_679_);
                crate::leanh::lean_inc(v___y_657_);
                crate::leanh::lean_inc_ref(v___y_656_);
                crate::leanh::lean_inc(v___y_655_);
                crate::leanh::lean_inc_ref(v___y_654_);
                crate::leanh::lean_inc(v___x_680_);
                v___x_681_ =
                    lean_infer_type(v___x_680_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
                if crate::leanh::lean_obj_tag(v___x_681_) == 0 {
                    v_a_682_ = crate::leanh::lean_ctor_get(v___x_681_, 0);
                    crate::leanh::lean_inc_n(v_a_682_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_681_, 1);
                    v___x_683_ = l_Lean_Meta_getDecLevel(
                        v_a_682_, v___y_654_, v___y_655_, v___y_656_, v___y_657_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_683_) == 0 {
                        v_a_684_ = crate::leanh::lean_ctor_get(v___x_683_, 0);
                        crate::leanh::lean_inc_n(v_a_684_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_683_, 1);
                        v___x_685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___closed__1;
                        v___x_686_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_fst_671_);
                        v___x_687_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_687_, 0, v_fst_671_);
                        crate::leanh::lean_ctor_set(v___x_687_, 1, v___x_686_);
                        v___x_688_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_688_, 0, v_a_684_);
                        crate::leanh::lean_ctor_set(v___x_688_, 1, v___x_687_);
                        crate::leanh::lean_inc_ref(v___x_688_);
                        v___x_689_ = l_Lean_mkConst(v___x_685_, v___x_688_);
                        crate::leanh::lean_inc(v___x_680_);
                        crate::leanh::lean_inc(v_fst_667_);
                        crate::leanh::lean_inc(v_a_682_);
                        v___x_690_ =
                            l_Lean_mkApp4(v___x_689_, v_a_682_, v_fst_667_, v___x_680_, v_fst_663_);
                        v___x_691_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1;
                        v___x_692_ = l_Lean_mkConst(v___x_691_, v___x_688_);
                        v___x_693_ = l_Lean_mkAppB(v___x_692_, v_a_682_, v_fst_667_);
                        v___x_694_ = l_Lean_mkLevelMax(v_fst_671_, v_a_684_);
                        v___x_695_ = l_Lean_Level_normalize(v___x_694_);
                        crate::leanh::lean_dec(v___x_694_);
                        v___x_696_ = lean_array_pop(v_snd_672_);
                        if v_isShared_675_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_674_, 1, v___x_696_);
                            crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_695_);
                            v___x_698_ = v___x_674_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_707_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_695_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_696_);
                            v___x_698_ = v_reuseFailAlloc_707_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_682_);
                        crate::leanh::lean_del_object(v___x_674_);
                        crate::leanh::lean_dec(v_snd_672_);
                        crate::leanh::lean_dec(v_fst_671_);
                        crate::leanh::lean_del_object(v___x_669_);
                        crate::leanh::lean_dec(v_fst_667_);
                        crate::leanh::lean_del_object(v___x_665_);
                        crate::leanh::lean_dec(v_fst_663_);
                        crate::leanh::lean_dec(v_a_652_);
                        v_a_708_ = crate::leanh::lean_ctor_get(v___x_683_, 0);
                        v_isSharedCheck_715_ = (!crate::leanh::lean_is_exclusive(v___x_683_)) as u8;
                        if v_isSharedCheck_715_ == 0 {
                            v___x_710_ = v___x_683_;
                            v_isShared_711_ = v_isSharedCheck_715_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_708_);
                            crate::leanh::lean_dec(v___x_683_);
                            v___x_710_ = crate::leanh::lean_box(0);
                            v_isShared_711_ = v_isSharedCheck_715_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_674_);
                    crate::leanh::lean_dec(v_snd_672_);
                    crate::leanh::lean_dec(v_fst_671_);
                    crate::leanh::lean_del_object(v___x_669_);
                    crate::leanh::lean_dec(v_fst_667_);
                    crate::leanh::lean_del_object(v___x_665_);
                    crate::leanh::lean_dec(v_fst_663_);
                    crate::leanh::lean_dec(v_a_652_);
                    v_a_716_ = crate::leanh::lean_ctor_get(v___x_681_, 0);
                    v_isSharedCheck_723_ = (!crate::leanh::lean_is_exclusive(v___x_681_)) as u8;
                    if v_isSharedCheck_723_ == 0 {
                        v___x_718_ = v___x_681_;
                        v_isShared_719_ = v_isSharedCheck_723_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_716_);
                        crate::leanh::lean_dec(v___x_681_);
                        v___x_718_ = crate::leanh::lean_box(0);
                        v_isShared_719_ = v_isSharedCheck_723_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_670_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_669_, 1, v___x_698_);
                    crate::leanh::lean_ctor_set(v___x_669_, 0, v___x_693_);
                    v___x_700_ = v___x_669_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_706_, 1, v___x_698_);
                    v___x_700_ = v_reuseFailAlloc_706_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_665_, 1, v___x_700_);
                    crate::leanh::lean_ctor_set(v___x_665_, 0, v___x_690_);
                    v___x_702_ = v___x_665_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_700_);
                    v___x_702_ = v_reuseFailAlloc_705_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_703_ = lean_nat_add(v_a_652_, v___x_678_);
                crate::leanh::lean_dec(v_a_652_);
                v_a_652_ = v___x_703_;
                v_b_653_ = v___x_702_;
                state = 0;
                continue;
            }
            7 => {
                if v_isShared_711_ == 0 {
                    v___x_713_ = v___x_710_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
                    v___x_713_ = v_reuseFailAlloc_714_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_713_;
            }
            9 => {
                if v_isShared_719_ == 0 {
                    v___x_721_ = v___x_718_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
                    v___x_721_ = v_reuseFailAlloc_722_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg___boxed(
    mut v_upperBound_729_: *mut crate::leanh::LeanObject,
    mut v_a_730_: *mut crate::leanh::LeanObject,
    mut v_b_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(
        v_upperBound_729_,
        v_a_730_,
        v_b_731_,
        v___y_732_,
        v___y_733_,
        v___y_734_,
        v___y_735_,
    );
    crate::leanh::lean_dec(v___y_735_);
    crate::leanh::lean_dec_ref(v___y_734_);
    crate::leanh::lean_dec(v___y_733_);
    crate::leanh::lean_dec_ref(v___y_732_);
    crate::leanh::lean_dec(v_upperBound_729_);
    return v_res_737_;
}
pub unsafe fn l_Lean_Meta_mkProdMkN(
    mut v_es_742_: *mut crate::leanh::LeanObject,
    mut v_u_743_: *mut crate::leanh::LeanObject,
    mut v_a_744_: *mut crate::leanh::LeanObject,
    mut v_a_745_: *mut crate::leanh::LeanObject,
    mut v_a_746_: *mut crate::leanh::LeanObject,
    mut v_a_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: u8 = 0;
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tuple_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_777_: u8 = 0;
    let mut v_snd_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_783_: u8 = 0;
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut v_unused_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut v_a_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_796_: u8 = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_800_: u8 = 0;
    let mut v_a_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_804_: u8 = 0;
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_808_: u8 = 0;
    let mut v_a_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_812_: u8 = 0;
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_749_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_750_ = lean_array_get_size(v_es_742_);
                v___x_751_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
                if v___x_751_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_742_);
                    v___x_752_ = l_Lean_Meta_mkProdMkN___closed__1;
                    v___x_753_ = l_Lean_Level_succ___override(v_u_743_);
                    v___x_754_ = crate::leanh::lean_box(0);
                    v___x_755_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_755_, 0, v___x_753_);
                    crate::leanh::lean_ctor_set(v___x_755_, 1, v___x_754_);
                    crate::leanh::lean_inc_ref(v___x_755_);
                    v___x_756_ = l_Lean_mkConst(v___x_752_, v___x_755_);
                    v___x_757_ = l_Lean_Meta_mkProdN___closed__1;
                    v___x_758_ = l_Lean_mkConst(v___x_757_, v___x_755_);
                    v___x_759_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_759_, 0, v___x_756_);
                    crate::leanh::lean_ctor_set(v___x_759_, 1, v___x_758_);
                    v___x_760_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_760_, 0, v___x_759_);
                    return v___x_760_;
                } else {
                    crate::leanh::lean_dec(v_u_743_);
                    v___x_761_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_762_ = lean_nat_sub(v___x_750_, v___x_761_);
                    v_tuple_763_ = lean_array_fget(v_es_742_, v___x_762_);
                    crate::leanh::lean_dec(v___x_762_);
                    crate::leanh::lean_inc(v_a_747_);
                    crate::leanh::lean_inc_ref(v_a_746_);
                    crate::leanh::lean_inc(v_a_745_);
                    crate::leanh::lean_inc_ref(v_a_744_);
                    crate::leanh::lean_inc(v_tuple_763_);
                    v___x_764_ =
                        lean_infer_type(v_tuple_763_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
                    if crate::leanh::lean_obj_tag(v___x_764_) == 0 {
                        v_a_765_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                        crate::leanh::lean_inc_n(v_a_765_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_764_, 1);
                        v___x_766_ = l_Lean_Meta_getDecLevel(
                            v_a_765_, v_a_744_, v_a_745_, v_a_746_, v_a_747_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_766_) == 0 {
                            v_a_767_ = crate::leanh::lean_ctor_get(v___x_766_, 0);
                            crate::leanh::lean_inc(v_a_767_);
                            crate::leanh::lean_dec_ref_known(v___x_766_, 1);
                            v___x_768_ = lean_array_pop(v_es_742_);
                            v___x_769_ = lean_array_get_size(v___x_768_);
                            v___x_770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_770_, 0, v_a_767_);
                            crate::leanh::lean_ctor_set(v___x_770_, 1, v___x_768_);
                            v___x_771_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_771_, 0, v_a_765_);
                            crate::leanh::lean_ctor_set(v___x_771_, 1, v___x_770_);
                            v___x_772_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_772_, 0, v_tuple_763_);
                            crate::leanh::lean_ctor_set(v___x_772_, 1, v___x_771_);
                            v___x_773_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(v___x_769_, v___x_749_, v___x_772_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
                            if crate::leanh::lean_obj_tag(v___x_773_) == 0 {
                                v_a_774_ = crate::leanh::lean_ctor_get(v___x_773_, 0);
                                v_isSharedCheck_792_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_773_)) as u8;
                                if v_isSharedCheck_792_ == 0 {
                                    v___x_776_ = v___x_773_;
                                    v_isShared_777_ = v_isSharedCheck_792_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_774_);
                                    crate::leanh::lean_dec(v___x_773_);
                                    v___x_776_ = crate::leanh::lean_box(0);
                                    v_isShared_777_ = v_isSharedCheck_792_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_793_ = crate::leanh::lean_ctor_get(v___x_773_, 0);
                                v_isSharedCheck_800_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_773_)) as u8;
                                if v_isSharedCheck_800_ == 0 {
                                    v___x_795_ = v___x_773_;
                                    v_isShared_796_ = v_isSharedCheck_800_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_793_);
                                    crate::leanh::lean_dec(v___x_773_);
                                    v___x_795_ = crate::leanh::lean_box(0);
                                    v_isShared_796_ = v_isSharedCheck_800_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_765_);
                            crate::leanh::lean_dec(v_tuple_763_);
                            crate::leanh::lean_dec_ref(v_es_742_);
                            v_a_801_ = crate::leanh::lean_ctor_get(v___x_766_, 0);
                            v_isSharedCheck_808_ =
                                (!crate::leanh::lean_is_exclusive(v___x_766_)) as u8;
                            if v_isSharedCheck_808_ == 0 {
                                v___x_803_ = v___x_766_;
                                v_isShared_804_ = v_isSharedCheck_808_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_801_);
                                crate::leanh::lean_dec(v___x_766_);
                                v___x_803_ = crate::leanh::lean_box(0);
                                v_isShared_804_ = v_isSharedCheck_808_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_tuple_763_);
                        crate::leanh::lean_dec_ref(v_es_742_);
                        v_a_809_ = crate::leanh::lean_ctor_get(v___x_764_, 0);
                        v_isSharedCheck_816_ = (!crate::leanh::lean_is_exclusive(v___x_764_)) as u8;
                        if v_isSharedCheck_816_ == 0 {
                            v___x_811_ = v___x_764_;
                            v_isShared_812_ = v_isSharedCheck_816_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_809_);
                            crate::leanh::lean_dec(v___x_764_);
                            v___x_811_ = crate::leanh::lean_box(0);
                            v_isShared_812_ = v_isSharedCheck_816_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_snd_778_ = crate::leanh::lean_ctor_get(v_a_774_, 1);
                crate::leanh::lean_inc(v_snd_778_);
                v_fst_779_ = crate::leanh::lean_ctor_get(v_a_774_, 0);
                crate::leanh::lean_inc(v_fst_779_);
                crate::leanh::lean_dec(v_a_774_);
                v_fst_780_ = crate::leanh::lean_ctor_get(v_snd_778_, 0);
                v_isSharedCheck_790_ = (!crate::leanh::lean_is_exclusive(v_snd_778_)) as u8;
                if v_isSharedCheck_790_ == 0 {
                    v_unused_791_ = crate::leanh::lean_ctor_get(v_snd_778_, 1);
                    crate::leanh::lean_dec(v_unused_791_);
                    v___x_782_ = v_snd_778_;
                    v_isShared_783_ = v_isSharedCheck_790_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_780_);
                    crate::leanh::lean_dec(v_snd_778_);
                    v___x_782_ = crate::leanh::lean_box(0);
                    v_isShared_783_ = v_isSharedCheck_790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_783_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_782_, 1, v_fst_780_);
                    crate::leanh::lean_ctor_set(v___x_782_, 0, v_fst_779_);
                    v___x_785_ = v___x_782_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 1, v_fst_780_);
                    v___x_785_ = v_reuseFailAlloc_789_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_777_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_776_, 0, v___x_785_);
                    v___x_787_ = v___x_776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_788_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
                    v___x_787_ = v_reuseFailAlloc_788_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_787_;
            }
            5 => {
                if v_isShared_796_ == 0 {
                    v___x_798_ = v___x_795_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_799_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
                    v___x_798_ = v_reuseFailAlloc_799_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_798_;
            }
            7 => {
                if v_isShared_804_ == 0 {
                    v___x_806_ = v___x_803_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
                    v___x_806_ = v_reuseFailAlloc_807_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_806_;
            }
            9 => {
                if v_isShared_812_ == 0 {
                    v___x_814_ = v___x_811_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
                    v___x_814_ = v_reuseFailAlloc_815_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkProdMkN___boxed(
    mut v_es_817_: *mut crate::leanh::LeanObject,
    mut v_u_818_: *mut crate::leanh::LeanObject,
    mut v_a_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_a_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
    mut v_a_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_824_ = l_Lean_Meta_mkProdMkN(v_es_817_, v_u_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_);
    crate::leanh::lean_dec(v_a_822_);
    crate::leanh::lean_dec_ref(v_a_821_);
    crate::leanh::lean_dec(v_a_820_);
    crate::leanh::lean_dec_ref(v_a_819_);
    return v_res_824_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(
    mut v_upperBound_825_: *mut crate::leanh::LeanObject,
    mut v_inst_826_: *mut crate::leanh::LeanObject,
    mut v_R_827_: *mut crate::leanh::LeanObject,
    mut v_a_828_: *mut crate::leanh::LeanObject,
    mut v_b_829_: *mut crate::leanh::LeanObject,
    mut v_c_830_: *mut crate::leanh::LeanObject,
    mut v___y_831_: *mut crate::leanh::LeanObject,
    mut v___y_832_: *mut crate::leanh::LeanObject,
    mut v___y_833_: *mut crate::leanh::LeanObject,
    mut v___y_834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___redArg(
        v_upperBound_825_,
        v_a_828_,
        v_b_829_,
        v___y_831_,
        v___y_832_,
        v___y_833_,
        v___y_834_,
    );
    return v___x_836_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0___boxed(
    mut v_upperBound_837_: *mut crate::leanh::LeanObject,
    mut v_inst_838_: *mut crate::leanh::LeanObject,
    mut v_R_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_b_841_: *mut crate::leanh::LeanObject,
    mut v_c_842_: *mut crate::leanh::LeanObject,
    mut v___y_843_: *mut crate::leanh::LeanObject,
    mut v___y_844_: *mut crate::leanh::LeanObject,
    mut v___y_845_: *mut crate::leanh::LeanObject,
    mut v___y_846_: *mut crate::leanh::LeanObject,
    mut v___y_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_848_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdMkN_spec__0(
        v_upperBound_837_,
        v_inst_838_,
        v_R_839_,
        v_a_840_,
        v_b_841_,
        v_c_842_,
        v___y_843_,
        v___y_844_,
        v___y_845_,
        v___y_846_,
    );
    crate::leanh::lean_dec(v___y_846_);
    crate::leanh::lean_dec_ref(v___y_845_);
    crate::leanh::lean_dec(v___y_844_);
    crate::leanh::lean_dec_ref(v___y_843_);
    crate::leanh::lean_dec(v_upperBound_837_);
    return v_res_848_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(
    mut v_msgData_849_: *mut crate::leanh::LeanObject,
    mut v___y_850_: *mut crate::leanh::LeanObject,
    mut v___y_851_: *mut crate::leanh::LeanObject,
    mut v___y_852_: *mut crate::leanh::LeanObject,
    mut v___y_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = lean_st_ref_get(v___y_853_);
    v_env_856_ = crate::leanh::lean_ctor_get(v___x_855_, 0);
    crate::leanh::lean_inc_ref(v_env_856_);
    crate::leanh::lean_dec(v___x_855_);
    v___x_857_ = lean_st_ref_get(v___y_851_);
    v_mctx_858_ = crate::leanh::lean_ctor_get(v___x_857_, 0);
    crate::leanh::lean_inc_ref(v_mctx_858_);
    crate::leanh::lean_dec(v___x_857_);
    v_lctx_859_ = crate::leanh::lean_ctor_get(v___y_850_, 2);
    v_options_860_ = crate::leanh::lean_ctor_get(v___y_852_, 2);
    crate::leanh::lean_inc_ref(v_options_860_);
    crate::leanh::lean_inc_ref(v_lctx_859_);
    v___x_861_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_861_, 0, v_env_856_);
    crate::leanh::lean_ctor_set(v___x_861_, 1, v_mctx_858_);
    crate::leanh::lean_ctor_set(v___x_861_, 2, v_lctx_859_);
    crate::leanh::lean_ctor_set(v___x_861_, 3, v_options_860_);
    v___x_862_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_862_, 0, v___x_861_);
    crate::leanh::lean_ctor_set(v___x_862_, 1, v_msgData_849_);
    v___x_863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_863_, 0, v___x_862_);
    return v___x_863_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0___boxed(
    mut v_msgData_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
    mut v___y_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
    mut v___y_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_870_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(v_msgData_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
    crate::leanh::lean_dec(v___y_868_);
    crate::leanh::lean_dec_ref(v___y_867_);
    crate::leanh::lean_dec(v___y_866_);
    crate::leanh::lean_dec_ref(v___y_865_);
    return v_res_870_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(
    mut v_msg_871_: *mut crate::leanh::LeanObject,
    mut v___y_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
    mut v___y_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_887_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_877_ = crate::leanh::lean_ctor_get(v___y_874_, 5);
                v___x_878_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getProdFields_spec__0_spec__0(v_msg_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
                v_a_879_ = crate::leanh::lean_ctor_get(v___x_878_, 0);
                v_isSharedCheck_887_ = (!crate::leanh::lean_is_exclusive(v___x_878_)) as u8;
                if v_isSharedCheck_887_ == 0 {
                    v___x_881_ = v___x_878_;
                    v_isShared_882_ = v_isSharedCheck_887_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_879_);
                    crate::leanh::lean_dec(v___x_878_);
                    v___x_881_ = crate::leanh::lean_box(0);
                    v_isShared_882_ = v_isSharedCheck_887_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_877_);
                v___x_883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_883_, 0, v_ref_877_);
                crate::leanh::lean_ctor_set(v___x_883_, 1, v_a_879_);
                if v_isShared_882_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_881_, 1);
                    crate::leanh::lean_ctor_set(v___x_881_, 0, v___x_883_);
                    v___x_885_ = v___x_881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_886_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
                    v___x_885_ = v_reuseFailAlloc_886_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_885_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg___boxed(
    mut v_msg_888_: *mut crate::leanh::LeanObject,
    mut v___y_889_: *mut crate::leanh::LeanObject,
    mut v___y_890_: *mut crate::leanh::LeanObject,
    mut v___y_891_: *mut crate::leanh::LeanObject,
    mut v___y_892_: *mut crate::leanh::LeanObject,
    mut v___y_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_894_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(
        v_msg_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_,
    );
    crate::leanh::lean_dec(v___y_892_);
    crate::leanh::lean_dec_ref(v___y_891_);
    crate::leanh::lean_dec(v___y_890_);
    crate::leanh::lean_dec_ref(v___y_889_);
    return v_res_894_;
}
pub unsafe fn _init_l_Lean_Meta_getProdFields___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = l_Lean_Meta_getProdFields___closed__0;
    v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
    return v___x_897_;
}
pub unsafe fn _init_l_Lean_Meta_getProdFields___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_Meta_getProdFields___closed__2;
    v___x_900_ = l_Lean_stringToMessageData(v___x_899_);
    return v___x_900_;
}
pub unsafe fn l_Lean_Meta_getProdFields(
    mut v_tuple_909_: *mut crate::leanh::LeanObject,
    mut v_tupleTy_910_: *mut crate::leanh::LeanObject,
    mut v_a_911_: *mut crate::leanh::LeanObject,
    mut v_a_912_: *mut crate::leanh::LeanObject,
    mut v_a_913_: *mut crate::leanh::LeanObject,
    mut v_a_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_920_: u8 = 0;
    let mut v___y_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: u8 = 0;
    let mut v_arg_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    let mut v_arg_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_956_: u8 = 0;
    let mut v_a_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_960_: u8 = 0;
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_916_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_tupleTy_910_, v_a_912_);
                if crate::leanh::lean_obj_tag(v___x_916_) == 0 {
                    v_a_917_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
                    v_isSharedCheck_956_ = (!crate::leanh::lean_is_exclusive(v___x_916_)) as u8;
                    if v_isSharedCheck_956_ == 0 {
                        v___x_919_ = v___x_916_;
                        v_isShared_920_ = v_isSharedCheck_956_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_917_);
                        crate::leanh::lean_dec(v___x_916_);
                        v___x_919_ = crate::leanh::lean_box(0);
                        v_isShared_920_ = v_isSharedCheck_956_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_tuple_909_);
                    v_a_957_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
                    v_isSharedCheck_964_ = (!crate::leanh::lean_is_exclusive(v___x_916_)) as u8;
                    if v_isSharedCheck_964_ == 0 {
                        v___x_959_ = v___x_916_;
                        v_isShared_960_ = v_isSharedCheck_964_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_957_);
                        crate::leanh::lean_dec(v___x_916_);
                        v___x_959_ = crate::leanh::lean_box(0);
                        v_isShared_960_ = v_isSharedCheck_964_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_917_);
                v___x_934_ = l_Lean_Expr_cleanupAnnotations(v_a_917_);
                v___x_935_ = l_Lean_Expr_isApp(v___x_934_);
                if v___x_935_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_934_);
                    crate::leanh::lean_del_object(v___x_919_);
                    v___y_922_ = v_a_911_;
                    v___y_923_ = v_a_912_;
                    v___y_924_ = v_a_913_;
                    v___y_925_ = v_a_914_;
                    state = 2;
                    continue;
                } else {
                    v_arg_936_ = crate::leanh::lean_ctor_get(v___x_934_, 1);
                    crate::leanh::lean_inc_ref(v_arg_936_);
                    v___x_937_ = l_Lean_Expr_appFnCleanup___redArg(v___x_934_);
                    v___x_938_ = l_Lean_Expr_isApp(v___x_937_);
                    if v___x_938_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_937_);
                        crate::leanh::lean_dec_ref(v_arg_936_);
                        crate::leanh::lean_del_object(v___x_919_);
                        v___y_922_ = v_a_911_;
                        v___y_923_ = v_a_912_;
                        v___y_924_ = v_a_913_;
                        v___y_925_ = v_a_914_;
                        state = 2;
                        continue;
                    } else {
                        v_arg_939_ = crate::leanh::lean_ctor_get(v___x_937_, 1);
                        crate::leanh::lean_inc_ref(v_arg_939_);
                        v___x_940_ = l_Lean_Expr_appFnCleanup___redArg(v___x_937_);
                        v___x_941_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_mkProdN_spec__0___redArg___closed__1;
                        v___x_942_ = l_Lean_Expr_isConstOf(v___x_940_, v___x_941_);
                        if v___x_942_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_940_);
                            crate::leanh::lean_dec_ref(v_arg_939_);
                            crate::leanh::lean_dec_ref(v_arg_936_);
                            crate::leanh::lean_del_object(v___x_919_);
                            v___y_922_ = v_a_911_;
                            v___y_923_ = v_a_912_;
                            v___y_924_ = v_a_913_;
                            v___y_925_ = v_a_914_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_917_);
                            v___x_943_ = l_Lean_Meta_getProdFields___closed__5;
                            v___x_944_ = l_Lean_Expr_constLevels_x21(v___x_940_);
                            crate::leanh::lean_dec_ref(v___x_940_);
                            crate::leanh::lean_inc(v___x_944_);
                            v___x_945_ = l_Lean_mkConst(v___x_943_, v___x_944_);
                            crate::leanh::lean_inc_ref(v_tuple_909_);
                            crate::leanh::lean_inc_ref_n(v_arg_936_, 2);
                            crate::leanh::lean_inc_ref_n(v_arg_939_, 2);
                            v___x_946_ =
                                l_Lean_mkApp3(v___x_945_, v_arg_939_, v_arg_936_, v_tuple_909_);
                            v___x_947_ = l_Lean_Meta_getProdFields___closed__7;
                            v___x_948_ = l_Lean_mkConst(v___x_947_, v___x_944_);
                            v___x_949_ =
                                l_Lean_mkApp3(v___x_948_, v_arg_939_, v_arg_936_, v_tuple_909_);
                            v___x_950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_949_);
                            crate::leanh::lean_ctor_set(v___x_950_, 1, v_arg_936_);
                            v___x_951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_951_, 0, v_arg_939_);
                            crate::leanh::lean_ctor_set(v___x_951_, 1, v___x_950_);
                            v___x_952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_952_, 0, v___x_946_);
                            crate::leanh::lean_ctor_set(v___x_952_, 1, v___x_951_);
                            if v_isShared_920_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_952_);
                                v___x_954_ = v___x_919_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_955_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
                                v___x_954_ = v_reuseFailAlloc_955_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_926_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_getProdFields___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_getProdFields___closed__1_once),
                    _init_l_Lean_Meta_getProdFields___closed__1,
                );
                v___x_927_ = l_Lean_MessageData_ofExpr(v_tuple_909_);
                v___x_928_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_928_, 0, v___x_926_);
                crate::leanh::lean_ctor_set(v___x_928_, 1, v___x_927_);
                v___x_929_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_getProdFields___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_getProdFields___closed__3_once),
                    _init_l_Lean_Meta_getProdFields___closed__3,
                );
                v___x_930_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_930_, 0, v___x_928_);
                crate::leanh::lean_ctor_set(v___x_930_, 1, v___x_929_);
                v___x_931_ = l_Lean_MessageData_ofExpr(v_a_917_);
                v___x_932_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_932_, 0, v___x_930_);
                crate::leanh::lean_ctor_set(v___x_932_, 1, v___x_931_);
                v___x_933_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(
                    v___x_932_, v___y_922_, v___y_923_, v___y_924_, v___y_925_,
                );
                return v___x_933_;
            }
            3 => {
                return v___x_954_;
            }
            4 => {
                if v_isShared_960_ == 0 {
                    v___x_962_ = v___x_959_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_963_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
                    v___x_962_ = v_reuseFailAlloc_963_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getProdFields___boxed(
    mut v_tuple_965_: *mut crate::leanh::LeanObject,
    mut v_tupleTy_966_: *mut crate::leanh::LeanObject,
    mut v_a_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
    mut v_a_970_: *mut crate::leanh::LeanObject,
    mut v_a_971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_972_ = l_Lean_Meta_getProdFields(
        v_tuple_965_,
        v_tupleTy_966_,
        v_a_967_,
        v_a_968_,
        v_a_969_,
        v_a_970_,
    );
    crate::leanh::lean_dec(v_a_970_);
    crate::leanh::lean_dec_ref(v_a_969_);
    crate::leanh::lean_dec(v_a_968_);
    crate::leanh::lean_dec_ref(v_a_967_);
    return v_res_972_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(
    mut v_00_u03b1_973_: *mut crate::leanh::LeanObject,
    mut v_msg_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
    mut v___y_976_: *mut crate::leanh::LeanObject,
    mut v___y_977_: *mut crate::leanh::LeanObject,
    mut v___y_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___redArg(
        v_msg_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_,
    );
    return v___x_980_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0___boxed(
    mut v_00_u03b1_981_: *mut crate::leanh::LeanObject,
    mut v_msg_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
    mut v___y_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
    mut v___y_986_: *mut crate::leanh::LeanObject,
    mut v___y_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_988_ = l_Lean_throwError___at___00Lean_Meta_getProdFields_spec__0(
        v_00_u03b1_981_,
        v_msg_982_,
        v___y_983_,
        v___y_984_,
        v___y_985_,
        v___y_986_,
    );
    crate::leanh::lean_dec(v___y_986_);
    crate::leanh::lean_dec_ref(v___y_985_);
    crate::leanh::lean_dec(v___y_984_);
    crate::leanh::lean_dec_ref(v___y_983_);
    return v_res_988_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_ProdN(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_ProdN(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_ProdN(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_ProdN(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_ProdN(builtin);
}
