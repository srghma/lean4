// Lean compiler output
// Module: Lean.Meta.HasNotBit
// Imports: Lean.Meta.Basic Lean.Meta.MatchUtil
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hasFVar,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkRawNatLit, l_Lean_reflBoolTrue,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::MatchUtil::{
    initialize_Lean_Meta_MatchUtil, l_Lean_Meta_matchNe_x3f, runtime_initialize_Lean_Meta_MatchUtil,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_lor, lean_nat_shiftl};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::lean_panic_fn_borrowed;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_5, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_mkHasNotBit___closed__0_value: LeanStringObject<4> = LeanStringObject {
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
static mut l_mkHasNotBit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut LeanObject;
pub static l_mkHasNotBit___closed__1_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [104, 97, 115, 78, 111, 116, 66, 105, 116, 0],
};
static mut l_mkHasNotBit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBit___closed__1_value) as *mut LeanObject;
static l_mkHasNotBit___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l_mkHasNotBit___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_mkHasNotBit___closed__2_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_mkHasNotBit___closed__1_value) as *mut LeanObject,
        6351501397486105973 as *mut LeanObject,
    ],
};
static mut l_mkHasNotBit___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBit___closed__2_value) as *mut LeanObject;
static mut l_mkHasNotBit___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBit___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_panic___at___00mkHasNotBitProof_spec__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_panic___at___00mkHasNotBitProof_spec__0___closed__0_value)
        as *mut LeanObject;
pub static l_mkHasNotBitProof___closed__0_value: LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        110, 101, 95, 111, 102, 95, 98, 101, 113, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
    ],
};
static mut l_mkHasNotBitProof___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__0_value) as *mut LeanObject;
static l_mkHasNotBitProof___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l_mkHasNotBitProof___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__0_value) as *mut LeanObject,
        1750192217580950936 as *mut LeanObject,
    ],
};
static mut l_mkHasNotBitProof___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__1_value) as *mut LeanObject;
static mut l_mkHasNotBitProof___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__3_value: LeanStringObject<3> = LeanStringObject {
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
static mut l_mkHasNotBitProof___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__3_value) as *mut LeanObject;
pub static l_mkHasNotBitProof___closed__4_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_mkHasNotBitProof___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__4_value) as *mut LeanObject;
static l_mkHasNotBitProof___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__3_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
pub static l_mkHasNotBitProof___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__5_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__4_value) as *mut LeanObject,
        13480818501600609864 as *mut LeanObject,
    ],
};
static mut l_mkHasNotBitProof___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__5_value) as *mut LeanObject;
static mut l_mkHasNotBitProof___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_mkHasNotBitProof___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_mkHasNotBitProof___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__9_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_mkHasNotBitProof___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__9_value) as *mut LeanObject;
pub static l_mkHasNotBitProof___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__9_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
static mut l_mkHasNotBitProof___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__10_value) as *mut LeanObject;
static mut l_mkHasNotBitProof___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__12_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 97, 108, 115, 101, 0],
};
static mut l_mkHasNotBitProof___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__12_value) as *mut LeanObject;
static l_mkHasNotBitProof___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__9_value) as *mut LeanObject,
        12882480457794858234 as *mut LeanObject,
    ],
};
pub static l_mkHasNotBitProof___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__13_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_mkHasNotBitProof___closed__12_value) as *mut LeanObject,
        15761733860085307253 as *mut LeanObject,
    ],
};
static mut l_mkHasNotBitProof___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__13_value) as *mut LeanObject;
static mut l_mkHasNotBitProof___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_mkHasNotBitProof___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_mkHasNotBitProof___closed__16_value: LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 72, 97, 115, 78, 111, 116, 66, 105, 116, 0,
    ],
};
static mut l_mkHasNotBitProof___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__16_value) as *mut LeanObject;
pub static l_mkHasNotBitProof___closed__17_value: LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        109, 107, 72, 97, 115, 78, 111, 116, 66, 105, 116, 80, 114, 111, 111, 102, 0,
    ],
};
static mut l_mkHasNotBitProof___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__17_value) as *mut LeanObject;
pub static l_mkHasNotBitProof___closed__18_value: LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_mkHasNotBitProof___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_mkHasNotBitProof___closed__18_value) as *mut LeanObject;
static mut l_mkHasNotBitProof___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkHasNotBitProof___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_refutableHasNotBit_x3f___closed__0_value: LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        101, 113, 95, 111, 102, 95, 98, 101, 113, 95, 101, 113, 95, 116, 114, 117, 101, 0,
    ],
};
static mut l_refutableHasNotBit_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__0_value) as *mut LeanObject;
static l_refutableHasNotBit_x3f___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_mkHasNotBit___closed__0_value) as *mut LeanObject,
        11442535297760353691 as *mut LeanObject,
    ],
};
pub static l_refutableHasNotBit_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__1_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__0_value) as *mut LeanObject,
        13284083376251288999 as *mut LeanObject,
    ],
};
static mut l_refutableHasNotBit_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__1_value) as *mut LeanObject;
static mut l_refutableHasNotBit_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_refutableHasNotBit_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_refutableHasNotBit_x3f___closed__3_value: LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        114, 101, 102, 117, 116, 97, 98, 108, 101, 72, 97, 115, 78, 111, 116, 66, 105, 116, 63, 0,
    ],
};
static mut l_refutableHasNotBit_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_refutableHasNotBit_x3f___closed__3_value) as *mut LeanObject;
static mut l_refutableHasNotBit_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_refutableHasNotBit_x3f___closed__4: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(
    mut v_as_298_: *mut LeanObject,
    mut v_sz_299_: usize,
    mut v_i_300_: usize,
    mut v_b_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_302_: u8 = 0;
    let mut v_a_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: usize = 0;
    let mut v___x_308_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_302_ = lean_usize_dec_lt(v_i_300_, v_sz_299_);
                if v___x_302_ == 0 {
                    return v_b_301_;
                } else {
                    v_a_303_ = lean_array_uget_borrowed(v_as_298_, v_i_300_);
                    v___x_304_ = lean_unsigned_to_nat(1);
                    v___x_305_ = lean_nat_shiftl(v___x_304_, v_a_303_);
                    v___x_306_ = lean_nat_lor(v_b_301_, v___x_305_);
                    lean_dec(v___x_305_);
                    lean_dec(v_b_301_);
                    v___x_307_ = 1usize;
                    v___x_308_ = lean_usize_add(v_i_300_, v___x_307_);
                    v_i_300_ = v___x_308_;
                    v_b_301_ = v___x_306_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0___boxed(
    mut v_as_310_: *mut LeanObject,
    mut v_sz_311_: *mut LeanObject,
    mut v_i_312_: *mut LeanObject,
    mut v_b_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_314_: usize = 0;
    let mut v_i_boxed_315_: usize = 0;
    let mut v_res_316_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_314_ = lean_unbox_usize(v_sz_311_);
    lean_dec(v_sz_311_);
    v_i_boxed_315_ = lean_unbox_usize(v_i_312_);
    lean_dec(v_i_312_);
    v_res_316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(v_as_310_, v_sz_boxed_314_, v_i_boxed_315_, v_b_313_);
    lean_dec_ref(v_as_310_);
    return v_res_316_;
}
pub unsafe fn _init_l_mkHasNotBit___closed__3() -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = lean_box(0);
    v___x_323_ = l_mkHasNotBit___closed__2;
    v___x_324_ = l_Lean_mkConst(v___x_323_, v___x_322_);
    return v___x_324_;
}
pub unsafe fn l_mkHasNotBit(
    mut v_e_325_: *mut LeanObject,
    mut v_ns_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mask_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_328_: usize = 0;
    let mut v___x_329_: usize = 0;
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    v_mask_327_ = lean_unsigned_to_nat(0);
    v_sz_328_ = lean_array_size(v_ns_326_);
    v___x_329_ = 0usize;
    v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00mkHasNotBit_spec__0(v_ns_326_, v_sz_328_, v___x_329_, v_mask_327_);
    v___x_331_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3),
        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3_once),
        _init_l_mkHasNotBit___closed__3,
    );
    v___x_332_ = l_Lean_mkRawNatLit(v___x_330_);
    v___x_333_ = l_Lean_mkAppB(v___x_331_, v___x_332_, v_e_325_);
    return v___x_333_;
}
pub unsafe fn l_mkHasNotBit___boxed(
    mut v_e_334_: *mut LeanObject,
    mut v_ns_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_336_: *mut LeanObject = core::ptr::null_mut();
    v_res_336_ = l_mkHasNotBit(v_e_334_, v_ns_335_);
    lean_dec_ref(v_ns_335_);
    return v_res_336_;
}
pub unsafe fn l_panic___at___00mkHasNotBitProof_spec__0(
    mut v_msg_338_: *mut LeanObject,
    mut v___y_339_: *mut LeanObject,
    mut v___y_340_: *mut LeanObject,
    mut v___y_341_: *mut LeanObject,
    mut v___y_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344__overap_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    v___f_344_ = l_panic___at___00mkHasNotBitProof_spec__0___closed__0;
    v___x_344__overap_345_ = lean_panic_fn_borrowed(v___f_344_, v_msg_338_);
    lean_inc(v___y_342_);
    lean_inc_ref(v___y_341_);
    lean_inc(v___y_340_);
    lean_inc_ref(v___y_339_);
    v___x_346_ = lean_apply_5(
        v___x_344__overap_345_,
        v___y_339_,
        v___y_340_,
        v___y_341_,
        v___y_342_,
        lean_box(0),
    );
    return v___x_346_;
}
pub unsafe fn l_panic___at___00mkHasNotBitProof_spec__0___boxed(
    mut v_msg_347_: *mut LeanObject,
    mut v___y_348_: *mut LeanObject,
    mut v___y_349_: *mut LeanObject,
    mut v___y_350_: *mut LeanObject,
    mut v___y_351_: *mut LeanObject,
    mut v___y_352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_353_: *mut LeanObject = core::ptr::null_mut();
    v_res_353_ = l_panic___at___00mkHasNotBitProof_spec__0(
        v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_,
    );
    lean_dec(v___y_351_);
    lean_dec_ref(v___y_350_);
    lean_dec(v___y_349_);
    lean_dec_ref(v___y_348_);
    return v_res_353_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__2() -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = lean_box(0);
    v___x_359_ = l_mkHasNotBitProof___closed__1;
    v___x_360_ = l_Lean_mkConst(v___x_359_, v___x_358_);
    return v___x_360_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__6() -> *mut LeanObject {
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    v___x_366_ = lean_unsigned_to_nat(1);
    v___x_367_ = l_Lean_Level_ofNat(v___x_366_);
    return v___x_367_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__7() -> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = lean_box(0);
    v___x_369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__6),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__6_once),
        _init_l_mkHasNotBitProof___closed__6,
    );
    v___x_370_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_370_, 0, v___x_369_);
    lean_ctor_set(v___x_370_, 1, v___x_368_);
    return v___x_370_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__8() -> *mut LeanObject {
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v___x_371_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__7),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__7_once),
        _init_l_mkHasNotBitProof___closed__7,
    );
    v___x_372_ = l_mkHasNotBitProof___closed__5;
    v___x_373_ = l_Lean_mkConst(v___x_372_, v___x_371_);
    return v___x_373_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__11() -> *mut LeanObject {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    v___x_377_ = lean_box(0);
    v___x_378_ = l_mkHasNotBitProof___closed__10;
    v___x_379_ = l_Lean_mkConst(v___x_378_, v___x_377_);
    return v___x_379_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__14() -> *mut LeanObject {
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v___x_384_ = lean_box(0);
    v___x_385_ = l_mkHasNotBitProof___closed__13;
    v___x_386_ = l_Lean_mkConst(v___x_385_, v___x_384_);
    return v___x_386_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__15() -> *mut LeanObject {
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_387_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__14),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__14_once),
        _init_l_mkHasNotBitProof___closed__14,
    );
    v___x_388_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__11),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__11_once),
        _init_l_mkHasNotBitProof___closed__11,
    );
    v___x_389_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__8),
        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__8_once),
        _init_l_mkHasNotBitProof___closed__8,
    );
    v___x_390_ = l_Lean_mkAppB(v___x_389_, v___x_388_, v___x_387_);
    return v___x_390_;
}
pub unsafe fn _init_l_mkHasNotBitProof___closed__19() -> *mut LeanObject {
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    v___x_394_ = l_mkHasNotBitProof___closed__18;
    v___x_395_ = lean_unsigned_to_nat(57);
    v___x_396_ = lean_unsigned_to_nat(33);
    v___x_397_ = l_mkHasNotBitProof___closed__17;
    v___x_398_ = l_mkHasNotBitProof___closed__16;
    v___x_399_ =
        l_mkPanicMessageWithDecl(v___x_398_, v___x_397_, v___x_396_, v___x_395_, v___x_394_);
    return v___x_399_;
}
pub unsafe fn l_mkHasNotBitProof(
    mut v_e_400_: *mut LeanObject,
    mut v_ns_401_: *mut LeanObject,
    mut v_a_402_: *mut LeanObject,
    mut v_a_403_: *mut LeanObject,
    mut v_a_404_: *mut LeanObject,
    mut v_a_405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v_val_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_425_: u8 = 0;
    let mut v_a_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_407_ = l_mkHasNotBit(v_e_400_, v_ns_401_);
                v___x_408_ =
                    l_Lean_Meta_matchNe_x3f(v___x_407_, v_a_402_, v_a_403_, v_a_404_, v_a_405_);
                if lean_obj_tag(v___x_408_) == 0 {
                    v_a_409_ = lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_425_ = (!lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_425_ == 0 {
                        v___x_411_ = v___x_408_;
                        v_isShared_412_ = v_isSharedCheck_425_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_409_);
                        lean_dec(v___x_408_);
                        v___x_411_ = lean_box(0);
                        v_isShared_412_ = v_isSharedCheck_425_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_426_ = lean_ctor_get(v___x_408_, 0);
                    v_isSharedCheck_433_ = (!lean_is_exclusive(v___x_408_)) as u8;
                    if v_isSharedCheck_433_ == 0 {
                        v___x_428_ = v___x_408_;
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_426_);
                        lean_dec(v___x_408_);
                        v___x_428_ = lean_box(0);
                        v_isShared_429_ = v_isSharedCheck_433_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_409_) == 1 {
                    v_val_413_ = lean_ctor_get(v_a_409_, 0);
                    lean_inc(v_val_413_);
                    lean_dec_ref_known(v_a_409_, 1);
                    v_snd_414_ = lean_ctor_get(v_val_413_, 1);
                    lean_inc(v_snd_414_);
                    lean_dec(v_val_413_);
                    v_fst_415_ = lean_ctor_get(v_snd_414_, 0);
                    lean_inc(v_fst_415_);
                    v_snd_416_ = lean_ctor_get(v_snd_414_, 1);
                    lean_inc(v_snd_416_);
                    lean_dec(v_snd_414_);
                    v___x_417_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__2),
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__2_once),
                        _init_l_mkHasNotBitProof___closed__2,
                    );
                    v___x_418_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__15),
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__15_once),
                        _init_l_mkHasNotBitProof___closed__15,
                    );
                    v___x_419_ = l_Lean_mkApp3(v___x_417_, v_fst_415_, v_snd_416_, v___x_418_);
                    if v_isShared_412_ == 0 {
                        lean_ctor_set(v___x_411_, 0, v___x_419_);
                        v___x_421_ = v___x_411_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
                        v___x_421_ = v_reuseFailAlloc_422_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_411_);
                    lean_dec(v_a_409_);
                    v___x_423_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__19),
                        core::ptr::addr_of_mut!(l_mkHasNotBitProof___closed__19_once),
                        _init_l_mkHasNotBitProof___closed__19,
                    );
                    v___x_424_ = l_panic___at___00mkHasNotBitProof_spec__0(
                        v___x_423_, v_a_402_, v_a_403_, v_a_404_, v_a_405_,
                    );
                    return v___x_424_;
                }
            }
            2 => {
                return v___x_421_;
            }
            3 => {
                if v_isShared_429_ == 0 {
                    v___x_431_ = v___x_428_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
                    v___x_431_ = v_reuseFailAlloc_432_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkHasNotBitProof___boxed(
    mut v_e_434_: *mut LeanObject,
    mut v_ns_435_: *mut LeanObject,
    mut v_a_436_: *mut LeanObject,
    mut v_a_437_: *mut LeanObject,
    mut v_a_438_: *mut LeanObject,
    mut v_a_439_: *mut LeanObject,
    mut v_a_440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_441_: *mut LeanObject = core::ptr::null_mut();
    v_res_441_ = l_mkHasNotBitProof(v_e_434_, v_ns_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
    lean_dec(v_a_439_);
    lean_dec_ref(v_a_438_);
    lean_dec(v_a_437_);
    lean_dec_ref(v_a_436_);
    lean_dec_ref(v_ns_435_);
    return v_res_441_;
}
pub unsafe fn l_isHasNotBit_x3f(mut v_e_442_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    v___x_443_ = l_Lean_Expr_cleanupAnnotations(v_e_442_);
    v___x_444_ = l_Lean_Expr_isApp(v___x_443_);
    if v___x_444_ == 0 {
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_443_);
        v___x_445_ = lean_box(0);
        return v___x_445_;
    } else {
        let mut v_arg_446_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: u8 = 0;
        v_arg_446_ = lean_ctor_get(v___x_443_, 1);
        lean_inc_ref(v_arg_446_);
        v___x_447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_443_);
        v___x_448_ = l_Lean_Expr_isApp(v___x_447_);
        if v___x_448_ == 0 {
            let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_447_);
            lean_dec_ref(v_arg_446_);
            v___x_449_ = lean_box(0);
            return v___x_449_;
        } else {
            let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_452_: u8 = 0;
            v___x_450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_447_);
            v___x_451_ = l_mkHasNotBit___closed__2;
            v___x_452_ = l_Lean_Expr_isConstOf(v___x_450_, v___x_451_);
            lean_dec_ref(v___x_450_);
            if v___x_452_ == 0 {
                let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_arg_446_);
                v___x_453_ = lean_box(0);
                return v___x_453_;
            } else {
                let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
                v___x_454_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_454_, 0, v_arg_446_);
                return v___x_454_;
            }
        }
    }
}
pub unsafe fn l_panic___at___00refutableHasNotBit_x3f_spec__0(
    mut v_msg_455_: *mut LeanObject,
    mut v___y_456_: *mut LeanObject,
    mut v___y_457_: *mut LeanObject,
    mut v___y_458_: *mut LeanObject,
    mut v___y_459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859__overap_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    v___f_461_ = l_panic___at___00mkHasNotBitProof_spec__0___closed__0;
    v___x_1859__overap_462_ = lean_panic_fn_borrowed(v___f_461_, v_msg_455_);
    lean_inc(v___y_459_);
    lean_inc_ref(v___y_458_);
    lean_inc(v___y_457_);
    lean_inc_ref(v___y_456_);
    v___x_463_ = lean_apply_5(
        v___x_1859__overap_462_,
        v___y_456_,
        v___y_457_,
        v___y_458_,
        v___y_459_,
        lean_box(0),
    );
    return v___x_463_;
}
pub unsafe fn l_panic___at___00refutableHasNotBit_x3f_spec__0___boxed(
    mut v_msg_464_: *mut LeanObject,
    mut v___y_465_: *mut LeanObject,
    mut v___y_466_: *mut LeanObject,
    mut v___y_467_: *mut LeanObject,
    mut v___y_468_: *mut LeanObject,
    mut v___y_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_470_: *mut LeanObject = core::ptr::null_mut();
    v_res_470_ = l_panic___at___00refutableHasNotBit_x3f_spec__0(
        v_msg_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_,
    );
    lean_dec(v___y_468_);
    lean_dec_ref(v___y_467_);
    lean_dec(v___y_466_);
    lean_dec_ref(v___y_465_);
    return v_res_470_;
}
pub unsafe fn _init_l_refutableHasNotBit_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = lean_box(0);
    v___x_476_ = l_refutableHasNotBit_x3f___closed__1;
    v___x_477_ = l_Lean_mkConst(v___x_476_, v___x_475_);
    return v___x_477_;
}
pub unsafe fn _init_l_refutableHasNotBit_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = l_mkHasNotBitProof___closed__18;
    v___x_480_ = lean_unsigned_to_nat(84);
    v___x_481_ = lean_unsigned_to_nat(53);
    v___x_482_ = l_refutableHasNotBit_x3f___closed__3;
    v___x_483_ = l_mkHasNotBitProof___closed__16;
    v___x_484_ =
        l_mkPanicMessageWithDecl(v___x_483_, v___x_482_, v___x_481_, v___x_480_, v___x_479_);
    return v___x_484_;
}
pub unsafe fn l_refutableHasNotBit_x3f(
    mut v_e_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_a_488_: *mut LeanObject,
    mut v_a_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_495_: u8 = 0;
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    let mut v_arg_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: u8 = 0;
    let mut v_arg_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: u8 = 0;
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_514_: u8 = 0;
    let mut v___x_515_: u8 = 0;
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_523_: u8 = 0;
    let mut v_snd_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_531_: u8 = 0;
    let mut v___x_532_: u8 = 0;
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_546_: u8 = 0;
    let mut v_a_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_550_: u8 = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut v_isSharedCheck_555_: u8 = 0;
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_561_: u8 = 0;
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_570_: u8 = 0;
    let mut v_a_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_578_: u8 = 0;
    let mut v_isSharedCheck_579_: u8 = 0;
    let mut v_a_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_583_: u8 = 0;
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_587_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_491_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_485_, v_a_487_);
                if lean_obj_tag(v___x_491_) == 0 {
                    v_a_492_ = lean_ctor_get(v___x_491_, 0);
                    v_isSharedCheck_579_ = (!lean_is_exclusive(v___x_491_)) as u8;
                    if v_isSharedCheck_579_ == 0 {
                        v___x_494_ = v___x_491_;
                        v_isShared_495_ = v_isSharedCheck_579_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_492_);
                        lean_dec(v___x_491_);
                        v___x_494_ = lean_box(0);
                        v_isShared_495_ = v_isSharedCheck_579_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_580_ = lean_ctor_get(v___x_491_, 0);
                    v_isSharedCheck_587_ = (!lean_is_exclusive(v___x_491_)) as u8;
                    if v_isSharedCheck_587_ == 0 {
                        v___x_582_ = v___x_491_;
                        v_isShared_583_ = v_isSharedCheck_587_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_580_);
                        lean_dec(v___x_491_);
                        v___x_582_ = lean_box(0);
                        v_isShared_583_ = v_isSharedCheck_587_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_501_ = l_Lean_Expr_cleanupAnnotations(v_a_492_);
                v___x_502_ = l_Lean_Expr_isApp(v___x_501_);
                if v___x_502_ == 0 {
                    lean_dec_ref(v___x_501_);
                    state = 2;
                    continue;
                } else {
                    v_arg_503_ = lean_ctor_get(v___x_501_, 1);
                    lean_inc_ref(v_arg_503_);
                    v___x_504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_501_);
                    v___x_505_ = l_Lean_Expr_isApp(v___x_504_);
                    if v___x_505_ == 0 {
                        lean_dec_ref(v___x_504_);
                        lean_dec_ref(v_arg_503_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_506_ = lean_ctor_get(v___x_504_, 1);
                        lean_inc_ref(v_arg_506_);
                        v___x_507_ = l_Lean_Expr_appFnCleanup___redArg(v___x_504_);
                        v___x_508_ = l_mkHasNotBit___closed__2;
                        v___x_509_ = l_Lean_Expr_isConstOf(v___x_507_, v___x_508_);
                        lean_dec_ref(v___x_507_);
                        if v___x_509_ == 0 {
                            lean_dec_ref(v_arg_506_);
                            lean_dec_ref(v_arg_503_);
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_494_);
                            lean_inc(v_a_489_);
                            lean_inc_ref(v_a_488_);
                            lean_inc(v_a_487_);
                            lean_inc_ref(v_a_486_);
                            v___x_510_ =
                                lean_whnf(v_arg_503_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
                            if lean_obj_tag(v___x_510_) == 0 {
                                v_a_511_ = lean_ctor_get(v___x_510_, 0);
                                v_isSharedCheck_570_ = (!lean_is_exclusive(v___x_510_)) as u8;
                                if v_isSharedCheck_570_ == 0 {
                                    v___x_513_ = v___x_510_;
                                    v_isShared_514_ = v_isSharedCheck_570_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_511_);
                                    lean_dec(v___x_510_);
                                    v___x_513_ = lean_box(0);
                                    v_isShared_514_ = v_isSharedCheck_570_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_arg_506_);
                                v_a_571_ = lean_ctor_get(v___x_510_, 0);
                                v_isSharedCheck_578_ = (!lean_is_exclusive(v___x_510_)) as u8;
                                if v_isSharedCheck_578_ == 0 {
                                    v___x_573_ = v___x_510_;
                                    v_isShared_574_ = v_isSharedCheck_578_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_571_);
                                    lean_dec(v___x_510_);
                                    v___x_573_ = lean_box(0);
                                    v_isShared_574_ = v_isSharedCheck_578_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_497_ = lean_box(0);
                if v_isShared_495_ == 0 {
                    lean_ctor_set(v___x_494_, 0, v___x_497_);
                    v___x_499_ = v___x_494_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
                    v___x_499_ = v_reuseFailAlloc_500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_499_;
            }
            4 => {
                v___x_515_ = l_Lean_Expr_hasFVar(v_a_511_);
                if v___x_515_ == 0 {
                    lean_del_object(v___x_513_);
                    v___x_516_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3),
                        core::ptr::addr_of_mut!(l_mkHasNotBit___closed__3_once),
                        _init_l_mkHasNotBit___closed__3,
                    );
                    v___x_517_ = l_Lean_mkAppB(v___x_516_, v_arg_506_, v_a_511_);
                    v___x_518_ =
                        l_Lean_Meta_matchNe_x3f(v___x_517_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
                    if lean_obj_tag(v___x_518_) == 0 {
                        v_a_519_ = lean_ctor_get(v___x_518_, 0);
                        lean_inc(v_a_519_);
                        lean_dec_ref_known(v___x_518_, 1);
                        if lean_obj_tag(v_a_519_) == 1 {
                            v_val_520_ = lean_ctor_get(v_a_519_, 0);
                            v_isSharedCheck_555_ = (!lean_is_exclusive(v_a_519_)) as u8;
                            if v_isSharedCheck_555_ == 0 {
                                v___x_522_ = v_a_519_;
                                v_isShared_523_ = v_isSharedCheck_555_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_val_520_);
                                lean_dec(v_a_519_);
                                v___x_522_ = lean_box(0);
                                v_isShared_523_ = v_isSharedCheck_555_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_519_);
                            v___x_556_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__4),
                                core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__4_once),
                                _init_l_refutableHasNotBit_x3f___closed__4,
                            );
                            v___x_557_ = l_panic___at___00refutableHasNotBit_x3f_spec__0(
                                v___x_556_, v_a_486_, v_a_487_, v_a_488_, v_a_489_,
                            );
                            return v___x_557_;
                        }
                    } else {
                        v_a_558_ = lean_ctor_get(v___x_518_, 0);
                        v_isSharedCheck_565_ = (!lean_is_exclusive(v___x_518_)) as u8;
                        if v_isSharedCheck_565_ == 0 {
                            v___x_560_ = v___x_518_;
                            v_isShared_561_ = v_isSharedCheck_565_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_558_);
                            lean_dec(v___x_518_);
                            v___x_560_ = lean_box(0);
                            v_isShared_561_ = v_isSharedCheck_565_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_511_);
                    lean_dec_ref(v_arg_506_);
                    v___x_566_ = lean_box(0);
                    if v_isShared_514_ == 0 {
                        lean_ctor_set(v___x_513_, 0, v___x_566_);
                        v___x_568_ = v___x_513_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
                        v___x_568_ = v_reuseFailAlloc_569_;
                        state = 14;
                        continue;
                    }
                }
            }
            5 => {
                v_snd_524_ = lean_ctor_get(v_val_520_, 1);
                lean_inc(v_snd_524_);
                lean_dec(v_val_520_);
                v_fst_525_ = lean_ctor_get(v_snd_524_, 0);
                lean_inc_n(v_fst_525_, 2);
                v_snd_526_ = lean_ctor_get(v_snd_524_, 1);
                lean_inc_n(v_snd_526_, 2);
                lean_dec(v_snd_524_);
                v___x_527_ = l_Lean_Meta_isExprDefEq(
                    v_fst_525_, v_snd_526_, v_a_486_, v_a_487_, v_a_488_, v_a_489_,
                );
                if lean_obj_tag(v___x_527_) == 0 {
                    v_a_528_ = lean_ctor_get(v___x_527_, 0);
                    v_isSharedCheck_546_ = (!lean_is_exclusive(v___x_527_)) as u8;
                    if v_isSharedCheck_546_ == 0 {
                        v___x_530_ = v___x_527_;
                        v_isShared_531_ = v_isSharedCheck_546_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_528_);
                        lean_dec(v___x_527_);
                        v___x_530_ = lean_box(0);
                        v_isShared_531_ = v_isSharedCheck_546_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_526_);
                    lean_dec(v_fst_525_);
                    lean_del_object(v___x_522_);
                    v_a_547_ = lean_ctor_get(v___x_527_, 0);
                    v_isSharedCheck_554_ = (!lean_is_exclusive(v___x_527_)) as u8;
                    if v_isSharedCheck_554_ == 0 {
                        v___x_549_ = v___x_527_;
                        v_isShared_550_ = v_isSharedCheck_554_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_547_);
                        lean_dec(v___x_527_);
                        v___x_549_ = lean_box(0);
                        v_isShared_550_ = v_isSharedCheck_554_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_532_ = (lean_unbox(v_a_528_) as u8);
                lean_dec(v_a_528_);
                if v___x_532_ == 0 {
                    lean_dec(v_snd_526_);
                    lean_dec(v_fst_525_);
                    lean_del_object(v___x_522_);
                    v___x_533_ = lean_box(0);
                    if v_isShared_531_ == 0 {
                        lean_ctor_set(v___x_530_, 0, v___x_533_);
                        v___x_535_ = v___x_530_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
                        v___x_535_ = v_reuseFailAlloc_536_;
                        state = 7;
                        continue;
                    }
                } else {
                    v___x_537_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__2),
                        core::ptr::addr_of_mut!(l_refutableHasNotBit_x3f___closed__2_once),
                        _init_l_refutableHasNotBit_x3f___closed__2,
                    );
                    v___x_538_ = l_Lean_reflBoolTrue;
                    v___x_539_ = l_Lean_mkApp3(v___x_537_, v_fst_525_, v_snd_526_, v___x_538_);
                    if v_isShared_523_ == 0 {
                        lean_ctor_set(v___x_522_, 0, v___x_539_);
                        v___x_541_ = v___x_522_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_539_);
                        v___x_541_ = v_reuseFailAlloc_545_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_535_;
            }
            8 => {
                if v_isShared_531_ == 0 {
                    lean_ctor_set(v___x_530_, 0, v___x_541_);
                    v___x_543_ = v___x_530_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
                    v___x_543_ = v_reuseFailAlloc_544_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_543_;
            }
            10 => {
                if v_isShared_550_ == 0 {
                    v___x_552_ = v___x_549_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
                    v___x_552_ = v_reuseFailAlloc_553_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_552_;
            }
            12 => {
                if v_isShared_561_ == 0 {
                    v___x_563_ = v___x_560_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
                    v___x_563_ = v_reuseFailAlloc_564_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_563_;
            }
            14 => {
                return v___x_568_;
            }
            15 => {
                if v_isShared_574_ == 0 {
                    v___x_576_ = v___x_573_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_576_;
            }
            17 => {
                if v_isShared_583_ == 0 {
                    v___x_585_ = v___x_582_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
                    v___x_585_ = v_reuseFailAlloc_586_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_585_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_refutableHasNotBit_x3f___boxed(
    mut v_e_588_: *mut LeanObject,
    mut v_a_589_: *mut LeanObject,
    mut v_a_590_: *mut LeanObject,
    mut v_a_591_: *mut LeanObject,
    mut v_a_592_: *mut LeanObject,
    mut v_a_593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_594_: *mut LeanObject = core::ptr::null_mut();
    v_res_594_ = l_refutableHasNotBit_x3f(v_e_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
    lean_dec(v_a_592_);
    lean_dec_ref(v_a_591_);
    lean_dec(v_a_590_);
    lean_dec_ref(v_a_589_);
    return v_res_594_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_HasNotBit(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_HasNotBit(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_HasNotBit(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Meta_MatchUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_HasNotBit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_HasNotBit(builtin);
}
