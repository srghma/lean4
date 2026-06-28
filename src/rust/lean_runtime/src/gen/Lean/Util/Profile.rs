// Lean compiler output
// Module: Lean.Util.Profile
// Imports: Init.Data.OfScientific Lean.Data.Options
use crate::r#gen::Init::Data::OfScientific::{
    initialize_Init_Data_OfScientific, lean_float_of_nat, runtime_initialize_Init_Data_OfScientific,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3};
use crate::r#gen::Init::System::IO::l_unsafeBaseIO___redArg;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{
    initialize_Lean_Data_Options, lean_register_option, runtime_initialize_Lean_Data_Options,
};
use crate::lean_imports_rs::Init::Data::Float::lean_float_div;
use crate::lean_imports_rs::Lean::Util::Profile::{
    lean_display_cumulative_profiling_times, lean_profileit,
};
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [112, 114, 111, 102, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2414248948310525751 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<145> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 145, m_capacity: 145, m_length: 144, m_data: [115, 104, 111, 119, 32, 101, 120, 99, 108, 117, 115, 105, 118, 101, 32, 101, 120, 101, 99, 117, 116, 105, 111, 110, 32, 116, 105, 109, 101, 115, 32, 111, 102, 32, 118, 97, 114, 105, 111, 117, 115, 32, 76, 101, 97, 110, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 10, 10, 83, 101, 101, 32, 97, 108, 115, 111, 32, 96, 116, 114, 97, 99, 101, 46, 112, 114, 111, 102, 105, 108, 101, 114, 96, 32, 102, 111, 114, 32, 97, 110, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 32, 112, 114, 111, 102, 105, 108, 105, 110, 103, 32, 115, 121, 115, 116, 101, 109, 32, 119, 105, 116, 104, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 100, 32, 111, 117, 116, 112, 117, 116, 46, 0]};
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,621993120627976798 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 0]};
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,2414248948310525751 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,18152899650020381639 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<93> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 93, m_capacity: 93, m_length: 92, m_data: [116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 105, 110, 32, 109, 105, 108, 108, 105, 115, 101, 99, 111, 110, 100, 115, 44, 32, 112, 114, 111, 102, 105, 108, 105, 110, 103, 32, 116, 105, 109, 101, 115, 32, 117, 110, 100, 101, 114, 32, 116, 104, 114, 101, 115, 104, 111, 108, 100, 32, 119, 105, 108, 108, 32, 110, 111, 116, 32, 98, 101, 32, 114, 101, 112, 111, 114, 116, 101, 100, 32, 105, 110, 100, 105, 118, 105, 100, 117, 97, 108, 108, 121, 0]};
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 100 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__2_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,621993120627976798 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__0_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,17699306925484844714 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static mut l_Lean_profiler_threshold_getSecs___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_profiler_threshold_getSecs___closed__0: f64 = 0.0;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(
    mut v_name_263_: *mut crate::leanh::LeanObject,
    mut v_decl_264_: *mut crate::leanh::LeanObject,
    mut v_ref_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: u8 = 0;
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_276_: u8 = 0;
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_281_: u8 = 0;
    let mut v_unused_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_286_: u8 = 0;
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_267_ = crate::leanh::lean_ctor_get(v_decl_264_, 0);
                v_descr_268_ = crate::leanh::lean_ctor_get(v_decl_264_, 1);
                v_deprecation_x3f_269_ = crate::leanh::lean_ctor_get(v_decl_264_, 2);
                v___x_270_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_271_ = (crate::leanh::lean_unbox(v_defValue_267_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_270_, 0 as u32, v___x_271_);
                crate::leanh::lean_inc(v_deprecation_x3f_269_);
                crate::leanh::lean_inc_ref(v_descr_268_);
                crate::leanh::lean_inc_n(v_name_263_, 2);
                v___x_272_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_272_, 0, v_name_263_);
                crate::leanh::lean_ctor_set(v___x_272_, 1, v_ref_265_);
                crate::leanh::lean_ctor_set(v___x_272_, 2, v___x_270_);
                crate::leanh::lean_ctor_set(v___x_272_, 3, v_descr_268_);
                crate::leanh::lean_ctor_set(v___x_272_, 4, v_deprecation_x3f_269_);
                v___x_273_ = lean_register_option(v_name_263_, v___x_272_);
                if crate::leanh::lean_obj_tag(v___x_273_) == 0 {
                    v_isSharedCheck_281_ = (!crate::leanh::lean_is_exclusive(v___x_273_)) as u8;
                    if v_isSharedCheck_281_ == 0 {
                        v_unused_282_ = crate::leanh::lean_ctor_get(v___x_273_, 0);
                        crate::leanh::lean_dec(v_unused_282_);
                        v___x_275_ = v___x_273_;
                        v_isShared_276_ = v_isSharedCheck_281_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_273_);
                        v___x_275_ = crate::leanh::lean_box(0);
                        v_isShared_276_ = v_isSharedCheck_281_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_263_);
                    v_a_283_ = crate::leanh::lean_ctor_get(v___x_273_, 0);
                    v_isSharedCheck_290_ = (!crate::leanh::lean_is_exclusive(v___x_273_)) as u8;
                    if v_isSharedCheck_290_ == 0 {
                        v___x_285_ = v___x_273_;
                        v_isShared_286_ = v_isSharedCheck_290_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_283_);
                        crate::leanh::lean_dec(v___x_273_);
                        v___x_285_ = crate::leanh::lean_box(0);
                        v_isShared_286_ = v_isSharedCheck_290_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_267_);
                v___x_277_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_277_, 0, v_name_263_);
                crate::leanh::lean_ctor_set(v___x_277_, 1, v_defValue_267_);
                if v_isShared_276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_275_, 0, v___x_277_);
                    v___x_279_ = v___x_275_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
                    v___x_279_ = v_reuseFailAlloc_280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_279_;
            }
            3 => {
                if v_isShared_286_ == 0 {
                    v___x_288_ = v___x_285_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
                    v___x_288_ = v_reuseFailAlloc_289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_291_: *mut crate::leanh::LeanObject,
    mut v_decl_292_: *mut crate::leanh::LeanObject,
    mut v_ref_293_: *mut crate::leanh::LeanObject,
    mut v_a_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_295_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v_name_291_, v_decl_292_, v_ref_293_);
    crate::leanh::lean_dec_ref(v_decl_292_);
    return v_res_295_;
}
pub unsafe fn l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_;
    v___x_311_ = l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_;
    v___x_312_ = l___private_Lean_Util_Profile_0__Lean_initFn___closed__5_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_;
    v___x_313_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4__spec__0(v___x_310_, v___x_311_, v___x_312_);
    return v___x_313_;
}
pub unsafe fn l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4____boxed(
    mut v_a_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
    return v_res_315_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(
    mut v_name_316_: *mut crate::leanh::LeanObject,
    mut v_decl_317_: *mut crate::leanh::LeanObject,
    mut v_ref_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_328_: u8 = 0;
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_333_: u8 = 0;
    let mut v_unused_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_338_: u8 = 0;
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_320_ = crate::leanh::lean_ctor_get(v_decl_317_, 0);
                v_descr_321_ = crate::leanh::lean_ctor_get(v_decl_317_, 1);
                v_deprecation_x3f_322_ = crate::leanh::lean_ctor_get(v_decl_317_, 2);
                crate::leanh::lean_inc(v_defValue_320_);
                v___x_323_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_323_, 0, v_defValue_320_);
                crate::leanh::lean_inc(v_deprecation_x3f_322_);
                crate::leanh::lean_inc_ref(v_descr_321_);
                crate::leanh::lean_inc_n(v_name_316_, 2);
                v___x_324_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_324_, 0, v_name_316_);
                crate::leanh::lean_ctor_set(v___x_324_, 1, v_ref_318_);
                crate::leanh::lean_ctor_set(v___x_324_, 2, v___x_323_);
                crate::leanh::lean_ctor_set(v___x_324_, 3, v_descr_321_);
                crate::leanh::lean_ctor_set(v___x_324_, 4, v_deprecation_x3f_322_);
                v___x_325_ = lean_register_option(v_name_316_, v___x_324_);
                if crate::leanh::lean_obj_tag(v___x_325_) == 0 {
                    v_isSharedCheck_333_ = (!crate::leanh::lean_is_exclusive(v___x_325_)) as u8;
                    if v_isSharedCheck_333_ == 0 {
                        v_unused_334_ = crate::leanh::lean_ctor_get(v___x_325_, 0);
                        crate::leanh::lean_dec(v_unused_334_);
                        v___x_327_ = v___x_325_;
                        v_isShared_328_ = v_isSharedCheck_333_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_325_);
                        v___x_327_ = crate::leanh::lean_box(0);
                        v_isShared_328_ = v_isSharedCheck_333_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_316_);
                    v_a_335_ = crate::leanh::lean_ctor_get(v___x_325_, 0);
                    v_isSharedCheck_342_ = (!crate::leanh::lean_is_exclusive(v___x_325_)) as u8;
                    if v_isSharedCheck_342_ == 0 {
                        v___x_337_ = v___x_325_;
                        v_isShared_338_ = v_isSharedCheck_342_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_335_);
                        crate::leanh::lean_dec(v___x_325_);
                        v___x_337_ = crate::leanh::lean_box(0);
                        v_isShared_338_ = v_isSharedCheck_342_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_320_);
                v___x_329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_329_, 0, v_name_316_);
                crate::leanh::lean_ctor_set(v___x_329_, 1, v_defValue_320_);
                if v_isShared_328_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_327_, 0, v___x_329_);
                    v___x_331_ = v___x_327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_329_);
                    v___x_331_ = v_reuseFailAlloc_332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_331_;
            }
            3 => {
                if v_isShared_338_ == 0 {
                    v___x_340_ = v___x_337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_341_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
                    v___x_340_ = v_reuseFailAlloc_341_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_343_: *mut crate::leanh::LeanObject,
    mut v_decl_344_: *mut crate::leanh::LeanObject,
    mut v_ref_345_: *mut crate::leanh::LeanObject,
    mut v_a_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v_name_343_, v_decl_344_, v_ref_345_);
    crate::leanh::lean_dec_ref(v_decl_344_);
    return v_res_347_;
}
pub unsafe fn l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = l___private_Lean_Util_Profile_0__Lean_initFn___closed__1_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_;
    v___x_363_ = l___private_Lean_Util_Profile_0__Lean_initFn___closed__3_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_;
    v___x_364_ = l___private_Lean_Util_Profile_0__Lean_initFn___closed__4_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_;
    v___x_365_ = l_Lean_Option_register___at___00__private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4__spec__0(v___x_362_, v___x_363_, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4____boxed(
    mut v_a_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
    return v_res_367_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(
    mut v_opts_368_: *mut crate::leanh::LeanObject,
    mut v_opt_369_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_370_ = crate::leanh::lean_ctor_get(v_opt_369_, 0);
    v_defValue_371_ = crate::leanh::lean_ctor_get(v_opt_369_, 1);
    v_map_372_ = crate::leanh::lean_ctor_get(v_opts_368_, 0);
    v___x_373_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_372_,
            v_name_370_,
        );
    if crate::leanh::lean_obj_tag(v___x_373_) == 0 {
        let mut v___x_374_: u8 = 0;
        v___x_374_ = (crate::leanh::lean_unbox(v_defValue_371_) as u8);
        return v___x_374_;
    } else {
        let mut v_val_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_375_ = crate::leanh::lean_ctor_get(v___x_373_, 0);
        crate::leanh::lean_inc(v_val_375_);
        crate::leanh::lean_dec_ref_known(v___x_373_, 1);
        if crate::leanh::lean_obj_tag(v_val_375_) == 1 {
            let mut v_v_376_: u8 = 0;
            v_v_376_ = crate::leanh::lean_ctor_get_uint8(v_val_375_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_375_, 0);
            return v_v_376_;
        } else {
            let mut v___x_377_: u8 = 0;
            crate::leanh::lean_dec(v_val_375_);
            v___x_377_ = (crate::leanh::lean_unbox(v_defValue_371_) as u8);
            return v___x_377_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0___boxed(
    mut v_opts_378_: *mut crate::leanh::LeanObject,
    mut v_opt_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_380_: u8 = 0;
    let mut v_r_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_380_ =
        l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(
            v_opts_378_,
            v_opt_379_,
        );
    crate::leanh::lean_dec_ref(v_opt_379_);
    crate::leanh::lean_dec_ref(v_opts_378_);
    v_r_381_ = crate::leanh::lean_box((v_res_380_) as usize);
    return v_r_381_;
}
pub unsafe fn lean_get_profiler(mut v_o_382_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: u8 = 0;
    v___x_383_ = l_Lean_profiler;
    v___x_384_ =
        l_Lean_Option_get___at___00__private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(
            v_o_382_, v___x_383_,
        );
    crate::leanh::lean_dec_ref(v_o_382_);
    return v___x_384_;
}
pub unsafe fn l___private_Lean_Util_Profile_0__Lean_get__profiler___boxed(
    mut v_o_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_386_: u8 = 0;
    let mut v_r_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = lean_get_profiler(v_o_385_);
    v_r_387_ = crate::leanh::lean_box((v_res_386_) as usize);
    return v_r_387_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(
    mut v_opts_388_: *mut crate::leanh::LeanObject,
    mut v_opt_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_390_ = crate::leanh::lean_ctor_get(v_opt_389_, 0);
    v_defValue_391_ = crate::leanh::lean_ctor_get(v_opt_389_, 1);
    v_map_392_ = crate::leanh::lean_ctor_get(v_opts_388_, 0);
    v___x_393_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_392_,
            v_name_390_,
        );
    if crate::leanh::lean_obj_tag(v___x_393_) == 0 {
        crate::leanh::lean_inc(v_defValue_391_);
        return v_defValue_391_;
    } else {
        let mut v_val_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_394_ = crate::leanh::lean_ctor_get(v___x_393_, 0);
        crate::leanh::lean_inc(v_val_394_);
        crate::leanh::lean_dec_ref_known(v___x_393_, 1);
        if crate::leanh::lean_obj_tag(v_val_394_) == 3 {
            let mut v_v_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_395_ = crate::leanh::lean_ctor_get(v_val_394_, 0);
            crate::leanh::lean_inc(v_v_395_);
            crate::leanh::lean_dec_ref_known(v_val_394_, 1);
            return v_v_395_;
        } else {
            crate::leanh::lean_dec(v_val_394_);
            crate::leanh::lean_inc(v_defValue_391_);
            return v_defValue_391_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0___boxed(
    mut v_opts_396_: *mut crate::leanh::LeanObject,
    mut v_opt_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_398_ =
        l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_opts_396_, v_opt_397_);
    crate::leanh::lean_dec_ref(v_opt_397_);
    crate::leanh::lean_dec_ref(v_opts_396_);
    return v_res_398_;
}
pub unsafe fn _init_l_Lean_profiler_threshold_getSecs___closed__0() -> f64 {
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: f64 = 0.0;
    v___x_399_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_400_ = lean_float_of_nat(v___x_399_);
    return v___x_400_;
}
pub unsafe fn lean_get_profiler_threshold(mut v_o_401_: *mut crate::leanh::LeanObject) -> f64 {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: f64 = 0.0;
    let mut v___x_405_: f64 = 0.0;
    let mut v___x_406_: f64 = 0.0;
    v___x_402_ = l_Lean_profiler_threshold;
    v___x_403_ =
        l_Lean_Option_get___at___00Lean_profiler_threshold_getSecs_spec__0(v_o_401_, v___x_402_);
    crate::leanh::lean_dec_ref(v_o_401_);
    v___x_404_ = lean_float_of_nat(v___x_403_);
    v___x_405_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(l_Lean_profiler_threshold_getSecs___closed__0),
        core::ptr::addr_of_mut!(l_Lean_profiler_threshold_getSecs___closed__0_once),
        _init_l_Lean_profiler_threshold_getSecs___closed__0,
    );
    v___x_406_ = lean_float_div(v___x_404_, v___x_405_);
    return v___x_406_;
}
pub unsafe fn l_Lean_profiler_threshold_getSecs___boxed(
    mut v_o_407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_408_: f64 = 0.0;
    let mut v_r_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_408_ = lean_get_profiler_threshold(v_o_407_);
    v_r_409_ = crate::leanh::lean_box_float(v_res_408_);
    return v_r_409_;
}
pub unsafe fn l_Lean_profileit___boxed(
    mut v_00_u03b1_415_: *mut crate::leanh::LeanObject,
    mut v_category_416_: *mut crate::leanh::LeanObject,
    mut v_opts_417_: *mut crate::leanh::LeanObject,
    mut v_fn_418_: *mut crate::leanh::LeanObject,
    mut v_decl_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_420_ = lean_profileit(v_category_416_, v_opts_417_, v_fn_418_, v_decl_419_);
    crate::leanh::lean_dec_ref(v_opts_417_);
    crate::leanh::lean_dec_ref(v_category_416_);
    return v_res_420_;
}
pub unsafe fn l_Lean_profileitIOUnsafe___redArg___lam__0(
    mut v_act_421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_431_: u8 = 0;
    let mut v_a_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_435_: u8 = 0;
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_423_ = crate::leanh::lean_apply_1(v_act_421_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v___x_423_) == 0 {
                    v_a_424_ = crate::leanh::lean_ctor_get(v___x_423_, 0);
                    v_isSharedCheck_431_ = (!crate::leanh::lean_is_exclusive(v___x_423_)) as u8;
                    if v_isSharedCheck_431_ == 0 {
                        v___x_426_ = v___x_423_;
                        v_isShared_427_ = v_isSharedCheck_431_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_424_);
                        crate::leanh::lean_dec(v___x_423_);
                        v___x_426_ = crate::leanh::lean_box(0);
                        v_isShared_427_ = v_isSharedCheck_431_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_432_ = crate::leanh::lean_ctor_get(v___x_423_, 0);
                    v_isSharedCheck_439_ = (!crate::leanh::lean_is_exclusive(v___x_423_)) as u8;
                    if v_isSharedCheck_439_ == 0 {
                        v___x_434_ = v___x_423_;
                        v_isShared_435_ = v_isSharedCheck_439_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_432_);
                        crate::leanh::lean_dec(v___x_423_);
                        v___x_434_ = crate::leanh::lean_box(0);
                        v_isShared_435_ = v_isSharedCheck_439_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_427_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_426_, 1);
                    v___x_429_ = v___x_426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_430_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
                    v___x_429_ = v_reuseFailAlloc_430_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_429_;
            }
            3 => {
                if v_isShared_435_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_434_, 0);
                    v___x_437_ = v___x_434_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
                    v___x_437_ = v_reuseFailAlloc_438_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_profileitIOUnsafe___redArg___lam__0___boxed(
    mut v_act_440_: *mut crate::leanh::LeanObject,
    mut v___y_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Lean_profileitIOUnsafe___redArg___lam__0(v_act_440_);
    return v_res_442_;
}
pub unsafe fn l_Lean_profileitIOUnsafe___redArg___lam__1(
    mut v___f_443_: *mut crate::leanh::LeanObject,
    mut v_x_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = l_unsafeBaseIO___redArg(v___f_443_);
    return v___x_445_;
}
pub unsafe fn l_Lean_profileitIOUnsafe___redArg(
    mut v_category_446_: *mut crate::leanh::LeanObject,
    mut v_opts_447_: *mut crate::leanh::LeanObject,
    mut v_act_448_: *mut crate::leanh::LeanObject,
    mut v_decl_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_457_: u8 = 0;
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_461_: u8 = 0;
    let mut v_a_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_465_: u8 = 0;
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_451_ = crate::leanh::lean_alloc_closure(
                    l_Lean_profileitIOUnsafe___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_451_, 0, v_act_448_);
                v___f_452_ = crate::leanh::lean_alloc_closure(
                    l_Lean_profileitIOUnsafe___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_452_, 0, v___f_451_);
                v___x_453_ = lean_profileit(v_category_446_, v_opts_447_, v___f_452_, v_decl_449_);
                if crate::leanh::lean_obj_tag(v___x_453_) == 0 {
                    v_a_454_ = crate::leanh::lean_ctor_get(v___x_453_, 0);
                    v_isSharedCheck_461_ = (!crate::leanh::lean_is_exclusive(v___x_453_)) as u8;
                    if v_isSharedCheck_461_ == 0 {
                        v___x_456_ = v___x_453_;
                        v_isShared_457_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_454_);
                        crate::leanh::lean_dec(v___x_453_);
                        v___x_456_ = crate::leanh::lean_box(0);
                        v_isShared_457_ = v_isSharedCheck_461_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_462_ = crate::leanh::lean_ctor_get(v___x_453_, 0);
                    v_isSharedCheck_469_ = (!crate::leanh::lean_is_exclusive(v___x_453_)) as u8;
                    if v_isSharedCheck_469_ == 0 {
                        v___x_464_ = v___x_453_;
                        v_isShared_465_ = v_isSharedCheck_469_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_462_);
                        crate::leanh::lean_dec(v___x_453_);
                        v___x_464_ = crate::leanh::lean_box(0);
                        v_isShared_465_ = v_isSharedCheck_469_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_457_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_456_, 1);
                    v___x_459_ = v___x_456_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_454_);
                    v___x_459_ = v_reuseFailAlloc_460_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_459_;
            }
            3 => {
                if v_isShared_465_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_464_, 0);
                    v___x_467_ = v___x_464_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
                    v___x_467_ = v_reuseFailAlloc_468_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_profileitIOUnsafe___redArg___boxed(
    mut v_category_470_: *mut crate::leanh::LeanObject,
    mut v_opts_471_: *mut crate::leanh::LeanObject,
    mut v_act_472_: *mut crate::leanh::LeanObject,
    mut v_decl_473_: *mut crate::leanh::LeanObject,
    mut v_a_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_475_ =
        l_Lean_profileitIOUnsafe___redArg(v_category_470_, v_opts_471_, v_act_472_, v_decl_473_);
    crate::leanh::lean_dec_ref(v_opts_471_);
    crate::leanh::lean_dec_ref(v_category_470_);
    return v_res_475_;
}
pub unsafe fn l_Lean_profileitIOUnsafe(
    mut v_00_u03b5_476_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_477_: *mut crate::leanh::LeanObject,
    mut v_category_478_: *mut crate::leanh::LeanObject,
    mut v_opts_479_: *mut crate::leanh::LeanObject,
    mut v_act_480_: *mut crate::leanh::LeanObject,
    mut v_decl_481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_483_ =
        l_Lean_profileitIOUnsafe___redArg(v_category_478_, v_opts_479_, v_act_480_, v_decl_481_);
    return v___x_483_;
}
pub unsafe fn l_Lean_profileitIOUnsafe___boxed(
    mut v_00_u03b5_484_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_485_: *mut crate::leanh::LeanObject,
    mut v_category_486_: *mut crate::leanh::LeanObject,
    mut v_opts_487_: *mut crate::leanh::LeanObject,
    mut v_act_488_: *mut crate::leanh::LeanObject,
    mut v_decl_489_: *mut crate::leanh::LeanObject,
    mut v_a_490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_491_ = l_Lean_profileitIOUnsafe(
        v_00_u03b5_484_,
        v_00_u03b1_485_,
        v_category_486_,
        v_opts_487_,
        v_act_488_,
        v_decl_489_,
    );
    crate::leanh::lean_dec_ref(v_opts_487_);
    crate::leanh::lean_dec_ref(v_category_486_);
    return v_res_491_;
}
pub unsafe fn l_Lean_profileitM___redArg___lam__0(
    mut v_category_492_: *mut crate::leanh::LeanObject,
    mut v_opts_493_: *mut crate::leanh::LeanObject,
    mut v_decl_494_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_495_: *mut crate::leanh::LeanObject,
    mut v_act_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_498_ =
        l_Lean_profileitIOUnsafe___redArg(v_category_492_, v_opts_493_, v_act_496_, v_decl_494_);
    return v___x_498_;
}
pub unsafe fn l_Lean_profileitM___redArg___lam__0___boxed(
    mut v_category_499_: *mut crate::leanh::LeanObject,
    mut v_opts_500_: *mut crate::leanh::LeanObject,
    mut v_decl_501_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_502_: *mut crate::leanh::LeanObject,
    mut v_act_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_505_ = l_Lean_profileitM___redArg___lam__0(
        v_category_499_,
        v_opts_500_,
        v_decl_501_,
        v_00_u03b2_502_,
        v_act_503_,
    );
    crate::leanh::lean_dec_ref(v_opts_500_);
    crate::leanh::lean_dec_ref(v_category_499_);
    return v_res_505_;
}
pub unsafe fn l_Lean_profileitM___redArg(
    mut v_inst_506_: *mut crate::leanh::LeanObject,
    mut v_category_507_: *mut crate::leanh::LeanObject,
    mut v_opts_508_: *mut crate::leanh::LeanObject,
    mut v_act_509_: *mut crate::leanh::LeanObject,
    mut v_decl_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_511_ = crate::leanh::lean_alloc_closure(
        l_Lean_profileitM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        3,
    );
    crate::leanh::lean_closure_set(v___f_511_, 0, v_category_507_);
    crate::leanh::lean_closure_set(v___f_511_, 1, v_opts_508_);
    crate::leanh::lean_closure_set(v___f_511_, 2, v_decl_510_);
    v___x_512_ = crate::leanh::lean_apply_3(
        v_inst_506_,
        crate::leanh::lean_box(0),
        v___f_511_,
        v_act_509_,
    );
    return v___x_512_;
}
pub unsafe fn l_Lean_profileitM(
    mut v_m_513_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_514_: *mut crate::leanh::LeanObject,
    mut v_inst_515_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_516_: *mut crate::leanh::LeanObject,
    mut v_category_517_: *mut crate::leanh::LeanObject,
    mut v_opts_518_: *mut crate::leanh::LeanObject,
    mut v_act_519_: *mut crate::leanh::LeanObject,
    mut v_decl_520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_521_ = l_Lean_profileitM___redArg(
        v_inst_515_,
        v_category_517_,
        v_opts_518_,
        v_act_519_,
        v_decl_520_,
    );
    return v___x_521_;
}
pub unsafe fn l_Lean_displayCumulativeProfilingTimes___boxed(
    mut v_a_00___x40___internal___hyg_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = lean_display_cumulative_profiling_times();
    return v_res_524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Profile(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_2256275618____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_profiler = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_profiler);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Util_Profile_0__Lean_initFn_00___x40_Lean_Util_Profile_3464325698____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_profiler_threshold = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_profiler_threshold);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Profile(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Profile(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Options(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Profile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Profile(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Profile(builtin);
}
