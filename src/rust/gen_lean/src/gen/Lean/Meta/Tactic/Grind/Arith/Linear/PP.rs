// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.PP
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Tactic.Grind.Arith.Linear.Model Lean.Meta.Tactic.Grind.Arith.Util Init.Omega
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Model::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model, l_Lean_Meta_Grind_Arith_Linear_mkModel,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types, l_Lean_Meta_Grind_Arith_Linear_linearExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Util, l_Lean_Meta_Grind_Arith_quoteIfArithTerm,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed,
};
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_nat_dec_eq,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 115, 115, 105, 103, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,4634307013023994764 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 58, 61, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [47, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0_value:
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
    m_data: [108, 105, 110, 97, 114, 105, 116, 104, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2411415118934503308 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        76, 105, 110, 97, 114, 105, 116, 104, 32, 97, 115, 115, 105, 103, 110, 109, 101, 110, 116,
        32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [76, 105, 110, 97, 114, 105, 116, 104, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3()
-> f64 {
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: f64 = 0.0;
    v___x_296_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_297_ = lean_float_of_nat(v___x_296_);
    return v___x_297_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__5;
    v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
    return v___x_301_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(
    mut v_as_303_: *mut crate::leanh::LeanObject,
    mut v_sz_304_: usize,
    mut v_i_305_: usize,
    mut v_b_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_315_: u8 = 0;
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: f64 = 0.0;
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_326_: u8 = 0;
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: usize = 0;
    let mut v___x_340_: usize = 0;
    let mut v_reuseFailAlloc_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: u8 = 0;
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_352_: u8 = 0;
    let mut v_isSharedCheck_353_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_308_ = lean_usize_dec_lt(v_i_305_, v_sz_304_);
                if v___x_308_ == 0 {
                    v___x_309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_309_, 0, v_b_306_);
                    return v___x_309_;
                } else {
                    v_a_310_ = lean_array_uget(v_as_303_, v_i_305_);
                    v_fst_311_ = crate::leanh::lean_ctor_get(v_a_310_, 0);
                    v_snd_312_ = crate::leanh::lean_ctor_get(v_a_310_, 1);
                    v_isSharedCheck_353_ = (!crate::leanh::lean_is_exclusive(v_a_310_)) as u8;
                    if v_isSharedCheck_353_ == 0 {
                        v___x_314_ = v_a_310_;
                        v_isShared_315_ = v_isSharedCheck_353_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_312_);
                        crate::leanh::lean_inc(v_fst_311_);
                        crate::leanh::lean_dec(v_a_310_);
                        v___x_314_ = crate::leanh::lean_box(0);
                        v_isShared_315_ = v_isSharedCheck_353_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0;
                v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__2;
                v___x_318_ = crate::leanh::lean_box(0);
                v___x_319_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3);
                v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4;
                v___x_321_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_321_, 0, v___x_317_);
                crate::leanh::lean_ctor_set(v___x_321_, 1, v___x_318_);
                crate::leanh::lean_ctor_set(v___x_321_, 2, v___x_320_);
                crate::leanh::lean_ctor_set_float(
                    v___x_321_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_319_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_321_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_319_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_321_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_308_,
                );
                v_num_322_ = crate::leanh::lean_ctor_get(v_snd_312_, 0);
                v_den_323_ = crate::leanh::lean_ctor_get(v_snd_312_, 1);
                v_isSharedCheck_352_ = (!crate::leanh::lean_is_exclusive(v_snd_312_)) as u8;
                if v_isSharedCheck_352_ == 0 {
                    v___x_325_ = v_snd_312_;
                    v_isShared_326_ = v_isSharedCheck_352_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_den_323_);
                    crate::leanh::lean_inc(v_num_322_);
                    crate::leanh::lean_dec(v_snd_312_);
                    v___x_325_ = crate::leanh::lean_box(0);
                    v_isShared_326_ = v_isSharedCheck_352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_327_ = l_Lean_Meta_Grind_Arith_quoteIfArithTerm(v_fst_311_);
                v___x_328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__6);
                if v_isShared_326_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_325_, 7);
                    crate::leanh::lean_ctor_set(v___x_325_, 1, v___x_328_);
                    crate::leanh::lean_ctor_set(v___x_325_, 0, v___x_327_);
                    v___x_330_ = v___x_325_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_351_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_327_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_351_, 1, v___x_328_);
                    v___x_330_ = v_reuseFailAlloc_351_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_343_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_344_ = lean_nat_dec_eq(v_den_323_, v___x_343_);
                if v___x_344_ == 0 {
                    v___x_345_ = l_Int_repr(v_num_322_);
                    crate::leanh::lean_dec(v_num_322_);
                    v___x_346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__7;
                    v___x_347_ = lean_string_append(v___x_345_, v___x_346_);
                    v___x_348_ = l_Nat_reprFast(v_den_323_);
                    v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
                    crate::leanh::lean_dec_ref(v___x_348_);
                    v___y_332_ = v___x_349_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_den_323_);
                    v___x_350_ = l_Int_repr(v_num_322_);
                    crate::leanh::lean_dec(v_num_322_);
                    v___y_332_ = v___x_350_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_333_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_333_, 0, v___y_332_);
                v___x_334_ = l_Lean_MessageData_ofFormat(v___x_333_);
                if v_isShared_315_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_314_, 7);
                    crate::leanh::lean_ctor_set(v___x_314_, 1, v___x_334_);
                    crate::leanh::lean_ctor_set(v___x_314_, 0, v___x_330_);
                    v___x_336_ = v___x_314_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_342_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_334_);
                    v___x_336_ = v_reuseFailAlloc_342_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_337_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_337_, 0, v___x_321_);
                crate::leanh::lean_ctor_set(v___x_337_, 1, v___x_336_);
                crate::leanh::lean_ctor_set(v___x_337_, 2, v___x_316_);
                v___x_338_ = lean_array_push(v_b_306_, v___x_337_);
                v___x_339_ = 1usize;
                v___x_340_ = lean_usize_add(v_i_305_, v___x_339_);
                v_i_305_ = v___x_340_;
                v_b_306_ = v___x_338_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___boxed(
    mut v_as_354_: *mut crate::leanh::LeanObject,
    mut v_sz_355_: *mut crate::leanh::LeanObject,
    mut v_i_356_: *mut crate::leanh::LeanObject,
    mut v_b_357_: *mut crate::leanh::LeanObject,
    mut v___y_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_359_: usize = 0;
    let mut v_i_boxed_360_: usize = 0;
    let mut v_res_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_359_ = crate::leanh::lean_unbox_usize(v_sz_355_);
    crate::leanh::lean_dec(v_sz_355_);
    v_i_boxed_360_ = crate::leanh::lean_unbox_usize(v_i_356_);
    crate::leanh::lean_dec(v_i_356_);
    v_res_361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_354_, v_sz_boxed_359_, v_i_boxed_360_, v_b_357_);
    crate::leanh::lean_dec_ref(v_as_354_);
    return v_res_361_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: u8 = 0;
    let mut v___x_367_: f64 = 0.0;
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_365_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__4;
    v___x_366_ = 1;
    v___x_367_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__3);
    v___x_368_ = crate::leanh::lean_box(0);
    v___x_369_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__1;
    v___x_370_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
    crate::leanh::lean_ctor_set(v___x_370_, 0, v___x_369_);
    crate::leanh::lean_ctor_set(v___x_370_, 1, v___x_368_);
    crate::leanh::lean_ctor_set(v___x_370_, 2, v___x_365_);
    crate::leanh::lean_ctor_set_float(
        v___x_370_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_367_,
    );
    crate::leanh::lean_ctor_set_float(
        v___x_370_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
        v___x_367_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_370_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
        v___x_366_,
    );
    return v___x_370_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__3;
    v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
    return v___x_373_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_375_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__5;
    v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
    return v___x_376_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(
    mut v_goal_377_: *mut crate::leanh::LeanObject,
    mut v_s_378_: *mut crate::leanh::LeanObject,
    mut v_a_379_: *mut crate::leanh::LeanObject,
    mut v_a_380_: *mut crate::leanh::LeanObject,
    mut v_a_381_: *mut crate::leanh::LeanObject,
    mut v_a_382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_id_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_390_: u8 = 0;
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: u8 = 0;
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_395_: usize = 0;
    let mut v___x_396_: usize = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_413_: u8 = 0;
    let mut v_a_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_417_: u8 = 0;
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_421_: u8 = 0;
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_426_: u8 = 0;
    let mut v_a_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_430_: u8 = 0;
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_384_ = crate::leanh::lean_ctor_get(v_s_378_, 0);
                crate::leanh::lean_inc(v_id_384_);
                v_type_385_ = crate::leanh::lean_ctor_get(v_s_378_, 2);
                crate::leanh::lean_inc_ref(v_type_385_);
                crate::leanh::lean_dec_ref(v_s_378_);
                v___x_386_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(
                    v_goal_377_,
                    v_id_384_,
                    v_a_379_,
                    v_a_380_,
                    v_a_381_,
                    v_a_382_,
                );
                crate::leanh::lean_dec(v_id_384_);
                if crate::leanh::lean_obj_tag(v___x_386_) == 0 {
                    v_a_387_ = crate::leanh::lean_ctor_get(v___x_386_, 0);
                    v_isSharedCheck_426_ = (!crate::leanh::lean_is_exclusive(v___x_386_)) as u8;
                    if v_isSharedCheck_426_ == 0 {
                        v___x_389_ = v___x_386_;
                        v_isShared_390_ = v_isSharedCheck_426_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_387_);
                        crate::leanh::lean_dec(v___x_386_);
                        v___x_389_ = crate::leanh::lean_box(0);
                        v_isShared_390_ = v_isSharedCheck_426_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_385_);
                    v_a_427_ = crate::leanh::lean_ctor_get(v___x_386_, 0);
                    v_isSharedCheck_434_ = (!crate::leanh::lean_is_exclusive(v___x_386_)) as u8;
                    if v_isSharedCheck_434_ == 0 {
                        v___x_429_ = v___x_386_;
                        v_isShared_430_ = v_isSharedCheck_434_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_427_);
                        crate::leanh::lean_dec(v___x_386_);
                        v___x_429_ = crate::leanh::lean_box(0);
                        v_isShared_430_ = v_isSharedCheck_434_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_391_ = lean_array_get_size(v_a_387_);
                v___x_392_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_393_ = lean_nat_dec_eq(v___x_391_, v___x_392_);
                if v___x_393_ == 0 {
                    crate::leanh::lean_del_object(v___x_389_);
                    v___x_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0;
                    v_sz_395_ = lean_array_size(v_a_387_);
                    v___x_396_ = 0usize;
                    v___x_397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_a_387_, v_sz_395_, v___x_396_, v___x_394_);
                    crate::leanh::lean_dec(v_a_387_);
                    if crate::leanh::lean_obj_tag(v___x_397_) == 0 {
                        v_a_398_ = crate::leanh::lean_ctor_get(v___x_397_, 0);
                        v_isSharedCheck_413_ = (!crate::leanh::lean_is_exclusive(v___x_397_)) as u8;
                        if v_isSharedCheck_413_ == 0 {
                            v___x_400_ = v___x_397_;
                            v_isShared_401_ = v_isSharedCheck_413_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_398_);
                            crate::leanh::lean_dec(v___x_397_);
                            v___x_400_ = crate::leanh::lean_box(0);
                            v_isShared_401_ = v_isSharedCheck_413_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_385_);
                        v_a_414_ = crate::leanh::lean_ctor_get(v___x_397_, 0);
                        v_isSharedCheck_421_ = (!crate::leanh::lean_is_exclusive(v___x_397_)) as u8;
                        if v_isSharedCheck_421_ == 0 {
                            v___x_416_ = v___x_397_;
                            v_isShared_417_ = v_isSharedCheck_421_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_414_);
                            crate::leanh::lean_dec(v___x_397_);
                            v___x_416_ = crate::leanh::lean_box(0);
                            v_isShared_417_ = v_isSharedCheck_421_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_387_);
                    crate::leanh::lean_dec_ref(v_type_385_);
                    v___x_422_ = crate::leanh::lean_box(0);
                    if v_isShared_390_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_389_, 0, v___x_422_);
                        v___x_424_ = v___x_389_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_425_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
                        v___x_424_ = v_reuseFailAlloc_425_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_402_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2,
                );
                v___x_403_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__4,
                );
                v___x_404_ = l_Lean_MessageData_ofExpr(v_type_385_);
                v___x_405_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_405_, 0, v___x_403_);
                crate::leanh::lean_ctor_set(v___x_405_, 1, v___x_404_);
                v___x_406_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__6,
                );
                v___x_407_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_407_, 0, v___x_405_);
                crate::leanh::lean_ctor_set(v___x_407_, 1, v___x_406_);
                v___x_408_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_408_, 0, v___x_402_);
                crate::leanh::lean_ctor_set(v___x_408_, 1, v___x_407_);
                crate::leanh::lean_ctor_set(v___x_408_, 2, v_a_398_);
                v___x_409_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_409_, 0, v___x_408_);
                if v_isShared_401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_400_, 0, v___x_409_);
                    v___x_411_ = v___x_400_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
                    v___x_411_ = v_reuseFailAlloc_412_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_411_;
            }
            4 => {
                if v_isShared_417_ == 0 {
                    v___x_419_ = v___x_416_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
                    v___x_419_ = v_reuseFailAlloc_420_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_419_;
            }
            6 => {
                return v___x_424_;
            }
            7 => {
                if v_isShared_430_ == 0 {
                    v___x_432_ = v___x_429_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
                    v___x_432_ = v_reuseFailAlloc_433_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___boxed(
    mut v_goal_435_: *mut crate::leanh::LeanObject,
    mut v_s_436_: *mut crate::leanh::LeanObject,
    mut v_a_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
    mut v_a_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
    mut v_a_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(
        v_goal_435_,
        v_s_436_,
        v_a_437_,
        v_a_438_,
        v_a_439_,
        v_a_440_,
    );
    crate::leanh::lean_dec(v_a_440_);
    crate::leanh::lean_dec_ref(v_a_439_);
    crate::leanh::lean_dec(v_a_438_);
    crate::leanh::lean_dec_ref(v_a_437_);
    crate::leanh::lean_dec_ref(v_goal_435_);
    return v_res_442_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(
    mut v_as_443_: *mut crate::leanh::LeanObject,
    mut v_sz_444_: usize,
    mut v_i_445_: usize,
    mut v_b_446_: *mut crate::leanh::LeanObject,
    mut v___y_447_: *mut crate::leanh::LeanObject,
    mut v___y_448_: *mut crate::leanh::LeanObject,
    mut v___y_449_: *mut crate::leanh::LeanObject,
    mut v___y_450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg(v_as_443_, v_sz_444_, v_i_445_, v_b_446_);
    return v___x_452_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___boxed(
    mut v_as_453_: *mut crate::leanh::LeanObject,
    mut v_sz_454_: *mut crate::leanh::LeanObject,
    mut v_i_455_: *mut crate::leanh::LeanObject,
    mut v_b_456_: *mut crate::leanh::LeanObject,
    mut v___y_457_: *mut crate::leanh::LeanObject,
    mut v___y_458_: *mut crate::leanh::LeanObject,
    mut v___y_459_: *mut crate::leanh::LeanObject,
    mut v___y_460_: *mut crate::leanh::LeanObject,
    mut v___y_461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_462_: usize = 0;
    let mut v_i_boxed_463_: usize = 0;
    let mut v_res_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_462_ = crate::leanh::lean_unbox_usize(v_sz_454_);
    crate::leanh::lean_dec(v_sz_454_);
    v_i_boxed_463_ = crate::leanh::lean_unbox_usize(v_i_455_);
    crate::leanh::lean_dec(v_i_455_);
    v_res_464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0(v_as_453_, v_sz_boxed_462_, v_i_boxed_463_, v_b_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
    crate::leanh::lean_dec(v___y_460_);
    crate::leanh::lean_dec_ref(v___y_459_);
    crate::leanh::lean_dec(v___y_458_);
    crate::leanh::lean_dec_ref(v___y_457_);
    crate::leanh::lean_dec_ref(v_as_453_);
    return v_res_464_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(
    mut v_goal_465_: *mut crate::leanh::LeanObject,
    mut v_as_466_: *mut crate::leanh::LeanObject,
    mut v_sz_467_: usize,
    mut v_i_468_: usize,
    mut v_b_469_: *mut crate::leanh::LeanObject,
    mut v___y_470_: *mut crate::leanh::LeanObject,
    mut v___y_471_: *mut crate::leanh::LeanObject,
    mut v___y_472_: *mut crate::leanh::LeanObject,
    mut v___y_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_475_: u8 = 0;
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: usize = 0;
    let mut v___x_483_: usize = 0;
    let mut v_val_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_490_: u8 = 0;
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_475_ = lean_usize_dec_lt(v_i_468_, v_sz_467_);
                if v___x_475_ == 0 {
                    v___x_476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_476_, 0, v_b_469_);
                    return v___x_476_;
                } else {
                    v_a_477_ = lean_array_uget_borrowed(v_as_466_, v_i_468_);
                    crate::leanh::lean_inc(v_a_477_);
                    v___x_478_ = l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f(
                        v_goal_465_,
                        v_a_477_,
                        v___y_470_,
                        v___y_471_,
                        v___y_472_,
                        v___y_473_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_478_) == 0 {
                        v_a_479_ = crate::leanh::lean_ctor_get(v___x_478_, 0);
                        crate::leanh::lean_inc(v_a_479_);
                        crate::leanh::lean_dec_ref_known(v___x_478_, 1);
                        if crate::leanh::lean_obj_tag(v_a_479_) == 1 {
                            v_val_485_ = crate::leanh::lean_ctor_get(v_a_479_, 0);
                            crate::leanh::lean_inc(v_val_485_);
                            crate::leanh::lean_dec_ref_known(v_a_479_, 1);
                            v___x_486_ = lean_array_push(v_b_469_, v_val_485_);
                            v_a_481_ = v___x_486_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_479_);
                            v_a_481_ = v_b_469_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_469_);
                        v_a_487_ = crate::leanh::lean_ctor_get(v___x_478_, 0);
                        v_isSharedCheck_494_ = (!crate::leanh::lean_is_exclusive(v___x_478_)) as u8;
                        if v_isSharedCheck_494_ == 0 {
                            v___x_489_ = v___x_478_;
                            v_isShared_490_ = v_isSharedCheck_494_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_487_);
                            crate::leanh::lean_dec(v___x_478_);
                            v___x_489_ = crate::leanh::lean_box(0);
                            v_isShared_490_ = v_isSharedCheck_494_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_482_ = 1usize;
                v___x_483_ = lean_usize_add(v_i_468_, v___x_482_);
                v_i_468_ = v___x_483_;
                v_b_469_ = v_a_481_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_490_ == 0 {
                    v___x_492_ = v___x_489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_493_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
                    v___x_492_ = v_reuseFailAlloc_493_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_492_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0___boxed(
    mut v_goal_495_: *mut crate::leanh::LeanObject,
    mut v_as_496_: *mut crate::leanh::LeanObject,
    mut v_sz_497_: *mut crate::leanh::LeanObject,
    mut v_i_498_: *mut crate::leanh::LeanObject,
    mut v_b_499_: *mut crate::leanh::LeanObject,
    mut v___y_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
    mut v___y_502_: *mut crate::leanh::LeanObject,
    mut v___y_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_505_: usize = 0;
    let mut v_i_boxed_506_: usize = 0;
    let mut v_res_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_505_ = crate::leanh::lean_unbox_usize(v_sz_497_);
    crate::leanh::lean_dec(v_sz_497_);
    v_i_boxed_506_ = crate::leanh::lean_unbox_usize(v_i_498_);
    crate::leanh::lean_dec(v_i_498_);
    v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_495_, v_as_496_, v_sz_boxed_505_, v_i_boxed_506_, v_b_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
    crate::leanh::lean_dec(v___y_503_);
    crate::leanh::lean_dec_ref(v___y_502_);
    crate::leanh::lean_dec(v___y_501_);
    crate::leanh::lean_dec_ref(v___y_500_);
    crate::leanh::lean_dec_ref(v_as_496_);
    crate::leanh::lean_dec_ref(v_goal_495_);
    return v_res_507_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__1;
    v___x_512_ = l_Lean_MessageData_ofFormat(v___x_511_);
    return v___x_512_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_pp_x3f(
    mut v_goal_513_: *mut crate::leanh::LeanObject,
    mut v_a_514_: *mut crate::leanh::LeanObject,
    mut v_a_515_: *mut crate::leanh::LeanObject,
    mut v_a_516_: *mut crate::leanh::LeanObject,
    mut v_a_517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgs_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_525_: usize = 0;
    let mut v___x_526_: usize = 0;
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_531_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: u8 = 0;
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_552_: u8 = 0;
    let mut v_a_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_556_: u8 = 0;
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_560_: u8 = 0;
    let mut v_a_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_564_: u8 = 0;
    let mut v_ref_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_573_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_519_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                v___x_520_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_519_, v_goal_513_);
                if crate::leanh::lean_obj_tag(v___x_520_) == 0 {
                    v_a_521_ = crate::leanh::lean_ctor_get(v___x_520_, 0);
                    crate::leanh::lean_inc(v_a_521_);
                    crate::leanh::lean_dec_ref_known(v___x_520_, 1);
                    v_structs_522_ = crate::leanh::lean_ctor_get(v_a_521_, 0);
                    crate::leanh::lean_inc_ref(v_structs_522_);
                    crate::leanh::lean_dec(v_a_521_);
                    v___x_523_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_msgs_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_ppStruct_x3f_spec__0___redArg___closed__0;
                    v_sz_525_ = lean_array_size(v_structs_522_);
                    v___x_526_ = 0usize;
                    v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_Arith_Linear_pp_x3f_spec__0(v_goal_513_, v_structs_522_, v_sz_525_, v___x_526_, v_msgs_524_, v_a_514_, v_a_515_, v_a_516_, v_a_517_);
                    crate::leanh::lean_dec_ref(v_structs_522_);
                    if crate::leanh::lean_obj_tag(v___x_527_) == 0 {
                        v_a_528_ = crate::leanh::lean_ctor_get(v___x_527_, 0);
                        v_isSharedCheck_552_ = (!crate::leanh::lean_is_exclusive(v___x_527_)) as u8;
                        if v_isSharedCheck_552_ == 0 {
                            v___x_530_ = v___x_527_;
                            v_isShared_531_ = v_isSharedCheck_552_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_528_);
                            crate::leanh::lean_dec(v___x_527_);
                            v___x_530_ = crate::leanh::lean_box(0);
                            v_isShared_531_ = v_isSharedCheck_552_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_553_ = crate::leanh::lean_ctor_get(v___x_527_, 0);
                        v_isSharedCheck_560_ = (!crate::leanh::lean_is_exclusive(v___x_527_)) as u8;
                        if v_isSharedCheck_560_ == 0 {
                            v___x_555_ = v___x_527_;
                            v_isShared_556_ = v_isSharedCheck_560_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_553_);
                            crate::leanh::lean_dec(v___x_527_);
                            v___x_555_ = crate::leanh::lean_box(0);
                            v_isShared_556_ = v_isSharedCheck_560_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_561_ = crate::leanh::lean_ctor_get(v___x_520_, 0);
                    v_isSharedCheck_573_ = (!crate::leanh::lean_is_exclusive(v___x_520_)) as u8;
                    if v_isSharedCheck_573_ == 0 {
                        v___x_563_ = v___x_520_;
                        v_isShared_564_ = v_isSharedCheck_573_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_561_);
                        crate::leanh::lean_dec(v___x_520_);
                        v___x_563_ = crate::leanh::lean_box(0);
                        v_isShared_564_ = v_isSharedCheck_573_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_532_ = lean_array_get_size(v_a_528_);
                v___x_533_ = lean_nat_dec_eq(v___x_532_, v___x_523_);
                if v___x_533_ == 0 {
                    v___x_534_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_535_ = lean_nat_dec_eq(v___x_532_, v___x_534_);
                    if v___x_535_ == 0 {
                        v___x_536_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_ppStruct_x3f___closed__2,
                        );
                        v___x_537_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2_once
                            ),
                            _init_l_Lean_Meta_Grind_Arith_Linear_pp_x3f___closed__2,
                        );
                        v___x_538_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_538_, 0, v___x_536_);
                        crate::leanh::lean_ctor_set(v___x_538_, 1, v___x_537_);
                        crate::leanh::lean_ctor_set(v___x_538_, 2, v_a_528_);
                        v___x_539_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_539_, 0, v___x_538_);
                        if v_isShared_531_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_539_);
                            v___x_541_ = v___x_530_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_542_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_539_);
                            v___x_541_ = v_reuseFailAlloc_542_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_543_ = lean_array_fget(v_a_528_, v___x_523_);
                        crate::leanh::lean_dec(v_a_528_);
                        v___x_544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_544_, 0, v___x_543_);
                        if v_isShared_531_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_544_);
                            v___x_546_ = v___x_530_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
                            v___x_546_ = v_reuseFailAlloc_547_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_528_);
                    v___x_548_ = crate::leanh::lean_box(0);
                    if v_isShared_531_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_548_);
                        v___x_550_ = v___x_530_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_551_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
                        v___x_550_ = v_reuseFailAlloc_551_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_541_;
            }
            3 => {
                return v___x_546_;
            }
            4 => {
                return v___x_550_;
            }
            5 => {
                if v_isShared_556_ == 0 {
                    v___x_558_ = v___x_555_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
                    v___x_558_ = v_reuseFailAlloc_559_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_558_;
            }
            7 => {
                v_ref_565_ = crate::leanh::lean_ctor_get(v_a_516_, 5);
                v___x_566_ = lean_io_error_to_string(v_a_561_);
                v___x_567_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_567_, 0, v___x_566_);
                v___x_568_ = l_Lean_MessageData_ofFormat(v___x_567_);
                crate::leanh::lean_inc(v_ref_565_);
                v___x_569_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_569_, 0, v_ref_565_);
                crate::leanh::lean_ctor_set(v___x_569_, 1, v___x_568_);
                if v_isShared_564_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_563_, 0, v___x_569_);
                    v___x_571_ = v___x_563_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
                    v___x_571_ = v_reuseFailAlloc_572_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_pp_x3f___boxed(
    mut v_goal_574_: *mut crate::leanh::LeanObject,
    mut v_a_575_: *mut crate::leanh::LeanObject,
    mut v_a_576_: *mut crate::leanh::LeanObject,
    mut v_a_577_: *mut crate::leanh::LeanObject,
    mut v_a_578_: *mut crate::leanh::LeanObject,
    mut v_a_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_580_ =
        l_Lean_Meta_Grind_Arith_Linear_pp_x3f(v_goal_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
    crate::leanh::lean_dec(v_a_578_);
    crate::leanh::lean_dec_ref(v_a_577_);
    crate::leanh::lean_dec(v_a_576_);
    crate::leanh::lean_dec_ref(v_a_575_);
    crate::leanh::lean_dec_ref(v_goal_574_);
    return v_res_580_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
}
