// Lean compiler output
// Module: Lean.Util.Heartbeats
// Imports: Lean.CoreM
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IO::l_IO_getNumHeartbeats___boxed;
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofFormat,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::IO::lean_io_get_num_heartbeats;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l_Lean_withHeartbeats___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_IO_getNumHeartbeats___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withHeartbeats___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_withHeartbeats___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_reportOutOfHeartbeats___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_reportOutOfHeartbeats___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_reportOutOfHeartbeats___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_reportOutOfHeartbeats___closed__1_value: crate::leanh::LeanStringObject<109> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 109,
        m_capacity: 109,
        m_length: 108,
        m_data: [
            96, 32, 115, 116, 111, 112, 112, 101, 100, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105,
            116, 32, 119, 97, 115, 32, 114, 117, 110, 110, 105, 110, 103, 32, 111, 117, 116, 32,
            111, 102, 32, 116, 105, 109, 101, 46, 10, 89, 111, 117, 32, 109, 97, 121, 32, 103, 101,
            116, 32, 98, 101, 116, 116, 101, 114, 32, 114, 101, 115, 117, 108, 116, 115, 32, 117,
            115, 105, 110, 103, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109,
            97, 120, 72, 101, 97, 114, 116, 98, 101, 97, 116, 115, 32, 48, 96, 46, 0,
        ],
    };
static mut l_Lean_reportOutOfHeartbeats___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_reportOutOfHeartbeats___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__0(
    mut v_start_400_: *mut crate::leanh::LeanObject,
    mut v_r_401_: *mut crate::leanh::LeanObject,
    mut v_toPure_402_: *mut crate::leanh::LeanObject,
    mut v_finish_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = lean_nat_sub(v_finish_403_, v_start_400_);
    v___x_405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_405_, 0, v_r_401_);
    crate::leanh::lean_ctor_set(v___x_405_, 1, v___x_404_);
    v___x_406_ = crate::leanh::lean_apply_2(v_toPure_402_, crate::leanh::lean_box(0), v___x_405_);
    return v___x_406_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__0___boxed(
    mut v_start_407_: *mut crate::leanh::LeanObject,
    mut v_r_408_: *mut crate::leanh::LeanObject,
    mut v_toPure_409_: *mut crate::leanh::LeanObject,
    mut v_finish_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Lean_withHeartbeats___redArg___lam__0(
        v_start_407_,
        v_r_408_,
        v_toPure_409_,
        v_finish_410_,
    );
    crate::leanh::lean_dec(v_finish_410_);
    crate::leanh::lean_dec(v_start_407_);
    return v_res_411_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__1(
    mut v_start_412_: *mut crate::leanh::LeanObject,
    mut v_toPure_413_: *mut crate::leanh::LeanObject,
    mut v_toBind_414_: *mut crate::leanh::LeanObject,
    mut v___x_415_: *mut crate::leanh::LeanObject,
    mut v_r_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_417_ = crate::leanh::lean_alloc_closure(
        l_Lean_withHeartbeats___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_417_, 0, v_start_412_);
    crate::leanh::lean_closure_set(v___f_417_, 1, v_r_416_);
    crate::leanh::lean_closure_set(v___f_417_, 2, v_toPure_413_);
    v___x_418_ = crate::leanh::lean_apply_4(
        v_toBind_414_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_415_,
        v___f_417_,
    );
    return v___x_418_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__2(
    mut v_toPure_419_: *mut crate::leanh::LeanObject,
    mut v_toBind_420_: *mut crate::leanh::LeanObject,
    mut v___x_421_: *mut crate::leanh::LeanObject,
    mut v_x_422_: *mut crate::leanh::LeanObject,
    mut v_start_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_toBind_420_);
    v___f_424_ = crate::leanh::lean_alloc_closure(
        l_Lean_withHeartbeats___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_424_, 0, v_start_423_);
    crate::leanh::lean_closure_set(v___f_424_, 1, v_toPure_419_);
    crate::leanh::lean_closure_set(v___f_424_, 2, v_toBind_420_);
    crate::leanh::lean_closure_set(v___f_424_, 3, v___x_421_);
    v___x_425_ = crate::leanh::lean_apply_4(
        v_toBind_420_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_422_,
        v___f_424_,
    );
    return v___x_425_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg(
    mut v_inst_427_: *mut crate::leanh::LeanObject,
    mut v_inst_428_: *mut crate::leanh::LeanObject,
    mut v_x_429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_430_ = crate::leanh::lean_ctor_get(v_inst_427_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_430_);
    v_toBind_431_ = crate::leanh::lean_ctor_get(v_inst_427_, 1);
    crate::leanh::lean_inc_n(v_toBind_431_, 2);
    crate::leanh::lean_dec_ref(v_inst_427_);
    v_toPure_432_ = crate::leanh::lean_ctor_get(v_toApplicative_430_, 1);
    crate::leanh::lean_inc(v_toPure_432_);
    crate::leanh::lean_dec_ref(v_toApplicative_430_);
    v___x_433_ = l_Lean_withHeartbeats___redArg___closed__0;
    v___x_434_ = crate::leanh::lean_apply_2(v_inst_428_, crate::leanh::lean_box(0), v___x_433_);
    crate::leanh::lean_inc(v___x_434_);
    v___f_435_ = crate::leanh::lean_alloc_closure(
        l_Lean_withHeartbeats___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_435_, 0, v_toPure_432_);
    crate::leanh::lean_closure_set(v___f_435_, 1, v_toBind_431_);
    crate::leanh::lean_closure_set(v___f_435_, 2, v___x_434_);
    crate::leanh::lean_closure_set(v___f_435_, 3, v_x_429_);
    v___x_436_ = crate::leanh::lean_apply_4(
        v_toBind_431_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_434_,
        v___f_435_,
    );
    return v___x_436_;
}
pub unsafe fn l_Lean_withHeartbeats(
    mut v_m_437_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_438_: *mut crate::leanh::LeanObject,
    mut v_inst_439_: *mut crate::leanh::LeanObject,
    mut v_inst_440_: *mut crate::leanh::LeanObject,
    mut v_x_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_442_ = l_Lean_withHeartbeats___redArg(v_inst_439_, v_inst_440_, v_x_441_);
    return v___x_442_;
}
pub unsafe fn l_Lean_getMaxHeartbeats___redArg(
    mut v_a_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_maxHeartbeats_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_maxHeartbeats_445_ = crate::leanh::lean_ctor_get(v_a_443_, 9);
    crate::leanh::lean_inc(v_maxHeartbeats_445_);
    v___x_446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_446_, 0, v_maxHeartbeats_445_);
    return v___x_446_;
}
pub unsafe fn l_Lean_getMaxHeartbeats___redArg___boxed(
    mut v_a_447_: *mut crate::leanh::LeanObject,
    mut v_a_448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Lean_getMaxHeartbeats___redArg(v_a_447_);
    crate::leanh::lean_dec_ref(v_a_447_);
    return v_res_449_;
}
pub unsafe fn l_Lean_getMaxHeartbeats(
    mut v_a_450_: *mut crate::leanh::LeanObject,
    mut v_a_451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_453_ = l_Lean_getMaxHeartbeats___redArg(v_a_450_);
    return v___x_453_;
}
pub unsafe fn l_Lean_getMaxHeartbeats___boxed(
    mut v_a_454_: *mut crate::leanh::LeanObject,
    mut v_a_455_: *mut crate::leanh::LeanObject,
    mut v_a_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Lean_getMaxHeartbeats(v_a_454_, v_a_455_);
    crate::leanh::lean_dec(v_a_455_);
    crate::leanh::lean_dec_ref(v_a_454_);
    return v_res_457_;
}
pub unsafe fn l_Lean_getInitHeartbeats___redArg(
    mut v_a_458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_initHeartbeats_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_initHeartbeats_460_ = crate::leanh::lean_ctor_get(v_a_458_, 8);
    crate::leanh::lean_inc(v_initHeartbeats_460_);
    v___x_461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_461_, 0, v_initHeartbeats_460_);
    return v___x_461_;
}
pub unsafe fn l_Lean_getInitHeartbeats___redArg___boxed(
    mut v_a_462_: *mut crate::leanh::LeanObject,
    mut v_a_463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Lean_getInitHeartbeats___redArg(v_a_462_);
    crate::leanh::lean_dec_ref(v_a_462_);
    return v_res_464_;
}
pub unsafe fn l_Lean_getInitHeartbeats(
    mut v_a_465_: *mut crate::leanh::LeanObject,
    mut v_a_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_468_ = l_Lean_getInitHeartbeats___redArg(v_a_465_);
    return v___x_468_;
}
pub unsafe fn l_Lean_getInitHeartbeats___boxed(
    mut v_a_469_: *mut crate::leanh::LeanObject,
    mut v_a_470_: *mut crate::leanh::LeanObject,
    mut v_a_471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_472_ = l_Lean_getInitHeartbeats(v_a_469_, v_a_470_);
    crate::leanh::lean_dec(v_a_470_);
    crate::leanh::lean_dec_ref(v_a_469_);
    return v_res_472_;
}
pub unsafe fn l_Lean_getRemainingHeartbeats___redArg(
    mut v_a_473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_475_ = l_Lean_getMaxHeartbeats___redArg(v_a_473_);
                v_a_476_ = crate::leanh::lean_ctor_get(v___x_475_, 0);
                crate::leanh::lean_inc(v_a_476_);
                crate::leanh::lean_dec_ref(v___x_475_);
                v___x_477_ = lean_io_get_num_heartbeats();
                v___x_478_ = l_Lean_getInitHeartbeats___redArg(v_a_473_);
                v_a_479_ = crate::leanh::lean_ctor_get(v___x_478_, 0);
                v_isSharedCheck_488_ = (!crate::leanh::lean_is_exclusive(v___x_478_)) as u8;
                if v_isSharedCheck_488_ == 0 {
                    v___x_481_ = v___x_478_;
                    v_isShared_482_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_479_);
                    crate::leanh::lean_dec(v___x_478_);
                    v___x_481_ = crate::leanh::lean_box(0);
                    v_isShared_482_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_483_ = lean_nat_sub(v___x_477_, v_a_479_);
                crate::leanh::lean_dec(v_a_479_);
                crate::leanh::lean_dec(v___x_477_);
                v___x_484_ = lean_nat_sub(v_a_476_, v___x_483_);
                crate::leanh::lean_dec(v___x_483_);
                crate::leanh::lean_dec(v_a_476_);
                if v_isShared_482_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_481_, 0, v___x_484_);
                    v___x_486_ = v___x_481_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
                    v___x_486_ = v_reuseFailAlloc_487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getRemainingHeartbeats___redArg___boxed(
    mut v_a_489_: *mut crate::leanh::LeanObject,
    mut v_a_490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_491_ = l_Lean_getRemainingHeartbeats___redArg(v_a_489_);
    crate::leanh::lean_dec_ref(v_a_489_);
    return v_res_491_;
}
pub unsafe fn l_Lean_getRemainingHeartbeats(
    mut v_a_492_: *mut crate::leanh::LeanObject,
    mut v_a_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_495_ = l_Lean_getRemainingHeartbeats___redArg(v_a_492_);
    return v___x_495_;
}
pub unsafe fn l_Lean_getRemainingHeartbeats___boxed(
    mut v_a_496_: *mut crate::leanh::LeanObject,
    mut v_a_497_: *mut crate::leanh::LeanObject,
    mut v_a_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Lean_getRemainingHeartbeats(v_a_496_, v_a_497_);
    crate::leanh::lean_dec(v_a_497_);
    crate::leanh::lean_dec_ref(v_a_496_);
    return v_res_499_;
}
pub unsafe fn l_Lean_heartbeatsPercent___redArg(
    mut v_a_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_509_: u8 = 0;
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_502_ = lean_io_get_num_heartbeats();
                v___x_503_ = l_Lean_getInitHeartbeats___redArg(v_a_500_);
                v_a_504_ = crate::leanh::lean_ctor_get(v___x_503_, 0);
                crate::leanh::lean_inc(v_a_504_);
                crate::leanh::lean_dec_ref(v___x_503_);
                v___x_505_ = l_Lean_getMaxHeartbeats___redArg(v_a_500_);
                v_a_506_ = crate::leanh::lean_ctor_get(v___x_505_, 0);
                v_isSharedCheck_517_ = (!crate::leanh::lean_is_exclusive(v___x_505_)) as u8;
                if v_isSharedCheck_517_ == 0 {
                    v___x_508_ = v___x_505_;
                    v_isShared_509_ = v_isSharedCheck_517_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_506_);
                    crate::leanh::lean_dec(v___x_505_);
                    v___x_508_ = crate::leanh::lean_box(0);
                    v_isShared_509_ = v_isSharedCheck_517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_510_ = lean_nat_sub(v___x_502_, v_a_504_);
                crate::leanh::lean_dec(v_a_504_);
                crate::leanh::lean_dec(v___x_502_);
                v___x_511_ = crate::leanh::lean_unsigned_to_nat(100);
                v___x_512_ = lean_nat_mul(v___x_510_, v___x_511_);
                crate::leanh::lean_dec(v___x_510_);
                v___x_513_ = lean_nat_div(v___x_512_, v_a_506_);
                crate::leanh::lean_dec(v_a_506_);
                crate::leanh::lean_dec(v___x_512_);
                if v_isShared_509_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_508_, 0, v___x_513_);
                    v___x_515_ = v___x_508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
                    v___x_515_ = v_reuseFailAlloc_516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_heartbeatsPercent___redArg___boxed(
    mut v_a_518_: *mut crate::leanh::LeanObject,
    mut v_a_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Lean_heartbeatsPercent___redArg(v_a_518_);
    crate::leanh::lean_dec_ref(v_a_518_);
    return v_res_520_;
}
pub unsafe fn l_Lean_heartbeatsPercent(
    mut v_a_521_: *mut crate::leanh::LeanObject,
    mut v_a_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_heartbeatsPercent___redArg(v_a_521_);
    return v___x_524_;
}
pub unsafe fn l_Lean_heartbeatsPercent___boxed(
    mut v_a_525_: *mut crate::leanh::LeanObject,
    mut v_a_526_: *mut crate::leanh::LeanObject,
    mut v_a_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_528_ = l_Lean_heartbeatsPercent(v_a_525_, v_a_526_);
    crate::leanh::lean_dec(v_a_526_);
    crate::leanh::lean_dec_ref(v_a_525_);
    return v_res_528_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(
    mut v___y_537_: u8,
    mut v_suppressElabErrors_538_: u8,
    mut v_x_539_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_539_) == 1 {
        let mut v_pre_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_540_ = crate::leanh::lean_ctor_get(v_x_539_, 0);
        match crate::leanh::lean_obj_tag(v_pre_540_) {
            1 => {
                let mut v_pre_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_541_ = crate::leanh::lean_ctor_get(v_pre_540_, 0);
                match crate::leanh::lean_obj_tag(v_pre_541_) {
                    0 => {
                        let mut v_str_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_545_: u8 = 0;
                        v_str_542_ = crate::leanh::lean_ctor_get(v_x_539_, 1);
                        v_str_543_ = crate::leanh::lean_ctor_get(v_pre_540_, 1);
                        v___x_544_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0;
                        v___x_545_ = lean_string_dec_eq(v_str_543_, v___x_544_);
                        if v___x_545_ == 0 {
                            let mut v___x_546_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_547_: u8 = 0;
                            v___x_546_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1;
                            v___x_547_ = lean_string_dec_eq(v_str_543_, v___x_546_);
                            if v___x_547_ == 0 {
                                return v___y_537_;
                            } else {
                                let mut v___x_548_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_549_: u8 = 0;
                                v___x_548_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2;
                                v___x_549_ = lean_string_dec_eq(v_str_542_, v___x_548_);
                                if v___x_549_ == 0 {
                                    return v___y_537_;
                                } else {
                                    return v_suppressElabErrors_538_;
                                }
                            }
                        } else {
                            let mut v___x_550_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_551_: u8 = 0;
                            v___x_550_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3;
                            v___x_551_ = lean_string_dec_eq(v_str_542_, v___x_550_);
                            if v___x_551_ == 0 {
                                return v___y_537_;
                            } else {
                                return v_suppressElabErrors_538_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_552_ = crate::leanh::lean_ctor_get(v_pre_541_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_552_) == 0 {
                            let mut v_str_553_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_554_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_555_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_556_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_557_: u8 = 0;
                            v_str_553_ = crate::leanh::lean_ctor_get(v_x_539_, 1);
                            v_str_554_ = crate::leanh::lean_ctor_get(v_pre_540_, 1);
                            v_str_555_ = crate::leanh::lean_ctor_get(v_pre_541_, 1);
                            v___x_556_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4;
                            v___x_557_ = lean_string_dec_eq(v_str_555_, v___x_556_);
                            if v___x_557_ == 0 {
                                return v___y_537_;
                            } else {
                                let mut v___x_558_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_559_: u8 = 0;
                                v___x_558_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5;
                                v___x_559_ = lean_string_dec_eq(v_str_554_, v___x_558_);
                                if v___x_559_ == 0 {
                                    return v___y_537_;
                                } else {
                                    let mut v___x_560_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_561_: u8 = 0;
                                    v___x_560_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6;
                                    v___x_561_ = lean_string_dec_eq(v_str_553_, v___x_560_);
                                    if v___x_561_ == 0 {
                                        return v___y_537_;
                                    } else {
                                        return v_suppressElabErrors_538_;
                                    }
                                }
                            }
                        } else {
                            return v___y_537_;
                        }
                    }
                    _ => {
                        return v___y_537_;
                    }
                }
            }
            0 => {
                let mut v_str_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_564_: u8 = 0;
                v_str_562_ = crate::leanh::lean_ctor_get(v_x_539_, 1);
                v___x_563_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7;
                v___x_564_ = lean_string_dec_eq(v_str_562_, v___x_563_);
                if v___x_564_ == 0 {
                    return v___y_537_;
                } else {
                    return v_suppressElabErrors_538_;
                }
            }
            _ => {
                return v___y_537_;
            }
        }
    } else {
        return v___y_537_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed(
    mut v___y_565_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_566_: *mut crate::leanh::LeanObject,
    mut v_x_567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2452__boxed_568_: u8 = 0;
    let mut v_suppressElabErrors_boxed_569_: u8 = 0;
    let mut v_res_570_: u8 = 0;
    let mut v_r_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_2452__boxed_568_ = (crate::leanh::lean_unbox(v___y_565_) as u8);
    v_suppressElabErrors_boxed_569_ = (crate::leanh::lean_unbox(v_suppressElabErrors_566_) as u8);
    v_res_570_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v___y_2452__boxed_568_, v_suppressElabErrors_boxed_569_, v_x_567_);
    crate::leanh::lean_dec(v_x_567_);
    v_r_571_ = crate::leanh::lean_box((v_res_570_) as usize);
    return v_r_571_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(
    mut v_opts_572_: *mut crate::leanh::LeanObject,
    mut v_opt_573_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_574_ = crate::leanh::lean_ctor_get(v_opt_573_, 0);
    v_defValue_575_ = crate::leanh::lean_ctor_get(v_opt_573_, 1);
    v_map_576_ = crate::leanh::lean_ctor_get(v_opts_572_, 0);
    v___x_577_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_576_,
            v_name_574_,
        );
    if crate::leanh::lean_obj_tag(v___x_577_) == 0 {
        let mut v___x_578_: u8 = 0;
        v___x_578_ = (crate::leanh::lean_unbox(v_defValue_575_) as u8);
        return v___x_578_;
    } else {
        let mut v_val_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_579_ = crate::leanh::lean_ctor_get(v___x_577_, 0);
        crate::leanh::lean_inc(v_val_579_);
        crate::leanh::lean_dec_ref_known(v___x_577_, 1);
        if crate::leanh::lean_obj_tag(v_val_579_) == 1 {
            let mut v_v_580_: u8 = 0;
            v_v_580_ = crate::leanh::lean_ctor_get_uint8(v_val_579_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_579_, 0);
            return v_v_580_;
        } else {
            let mut v___x_581_: u8 = 0;
            crate::leanh::lean_dec(v_val_579_);
            v___x_581_ = (crate::leanh::lean_unbox(v_defValue_575_) as u8);
            return v___x_581_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2___boxed(
    mut v_opts_582_: *mut crate::leanh::LeanObject,
    mut v_opt_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_584_: u8 = 0;
    let mut v_r_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_opts_582_, v_opt_583_);
    crate::leanh::lean_dec_ref(v_opt_583_);
    crate::leanh::lean_dec_ref(v_opts_582_);
    v_r_585_ = crate::leanh::lean_box((v_res_584_) as usize);
    return v_r_585_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_586_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_587_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0);
    v___x_588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_588_, 0, v___x_587_);
    return v___x_588_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
    v___x_590_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_591_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_591_, 0, v___x_590_);
    crate::leanh::lean_ctor_set(v___x_591_, 1, v___x_590_);
    crate::leanh::lean_ctor_set(v___x_591_, 2, v___x_590_);
    crate::leanh::lean_ctor_set(v___x_591_, 3, v___x_590_);
    crate::leanh::lean_ctor_set(v___x_591_, 4, v___x_589_);
    crate::leanh::lean_ctor_set(v___x_591_, 5, v___x_589_);
    crate::leanh::lean_ctor_set(v___x_591_, 6, v___x_589_);
    crate::leanh::lean_ctor_set(v___x_591_, 7, v___x_589_);
    crate::leanh::lean_ctor_set(v___x_591_, 8, v___x_589_);
    crate::leanh::lean_ctor_set(v___x_591_, 9, v___x_589_);
    return v___x_591_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_592_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_593_ = lean_mk_empty_array_with_capacity(v___x_592_);
    v___x_594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_594_, 0, v___x_593_);
    return v___x_594_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_595_: usize = 0;
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = 5usize;
    v___x_596_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_597_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_598_ = lean_mk_empty_array_with_capacity(v___x_597_);
    v___x_599_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3);
    v___x_600_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_600_, 0, v___x_599_);
    crate::leanh::lean_ctor_set(v___x_600_, 1, v___x_598_);
    crate::leanh::lean_ctor_set(v___x_600_, 2, v___x_596_);
    crate::leanh::lean_ctor_set(v___x_600_, 3, v___x_596_);
    crate::leanh::lean_ctor_set_usize(v___x_600_, 4, v___x_595_);
    return v___x_600_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = crate::leanh::lean_box(1);
    v___x_602_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4);
    v___x_603_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
    v___x_604_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_604_, 0, v___x_603_);
    crate::leanh::lean_ctor_set(v___x_604_, 1, v___x_602_);
    crate::leanh::lean_ctor_set(v___x_604_, 2, v___x_601_);
    return v___x_604_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(
    mut v_msgData_605_: *mut crate::leanh::LeanObject,
    mut v___y_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = lean_st_ref_get(v___y_607_);
    v_env_610_ = crate::leanh::lean_ctor_get(v___x_609_, 0);
    crate::leanh::lean_inc_ref(v_env_610_);
    crate::leanh::lean_dec(v___x_609_);
    v_options_611_ = crate::leanh::lean_ctor_get(v___y_606_, 2);
    v___x_612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2);
    v___x_613_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5);
    crate::leanh::lean_inc_ref(v_options_611_);
    v___x_614_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_614_, 0, v_env_610_);
    crate::leanh::lean_ctor_set(v___x_614_, 1, v___x_612_);
    crate::leanh::lean_ctor_set(v___x_614_, 2, v___x_613_);
    crate::leanh::lean_ctor_set(v___x_614_, 3, v_options_611_);
    v___x_615_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_615_, 0, v___x_614_);
    crate::leanh::lean_ctor_set(v___x_615_, 1, v_msgData_605_);
    v___x_616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_616_, 0, v___x_615_);
    return v___x_616_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_617_: *mut crate::leanh::LeanObject,
    mut v___y_618_: *mut crate::leanh::LeanObject,
    mut v___y_619_: *mut crate::leanh::LeanObject,
    mut v___y_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_617_, v___y_618_, v___y_619_);
    crate::leanh::lean_dec(v___y_619_);
    crate::leanh::lean_dec_ref(v___y_618_);
    return v_res_621_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(
    mut v_ref_623_: *mut crate::leanh::LeanObject,
    mut v_msgData_624_: *mut crate::leanh::LeanObject,
    mut v_severity_625_: u8,
    mut v_isSilent_626_: u8,
    mut v___y_627_: *mut crate::leanh::LeanObject,
    mut v___y_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_631_: u8 = 0;
    let mut v___y_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_636_: u8 = 0;
    let mut v___y_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_654_: u8 = 0;
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut v___y_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_668_: u8 = 0;
    let mut v___y_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_672_: u8 = 0;
    let mut v___y_673_: u8 = 0;
    let mut v___y_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_680_: u8 = 0;
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut v___y_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_693_: u8 = 0;
    let mut v___y_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_697_: u8 = 0;
    let mut v___y_698_: u8 = 0;
    let mut v___y_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_704_: u8 = 0;
    let mut v___y_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_708_: u8 = 0;
    let mut v___y_709_: u8 = 0;
    let mut v_ref_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v___y_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_720_: u8 = 0;
    let mut v___y_721_: u8 = 0;
    let mut v___y_722_: u8 = 0;
    let mut v___y_724_: u8 = 0;
    let mut v_fileName_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_729_: u8 = 0;
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: u8 = 0;
    let mut v___x_740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_714_ = 2;
                v___x_739_ = l_Lean_instBEqMessageSeverity_beq(v_severity_625_, v___x_714_);
                if v___x_739_ == 0 {
                    v___y_724_ = v___x_739_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_624_);
                    v___x_740_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_624_);
                    v___y_724_ = v___x_740_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_640_ = lean_st_ref_take(v___y_639_);
                v_currNamespace_641_ = crate::leanh::lean_ctor_get(v___y_638_, 6);
                v_openDecls_642_ = crate::leanh::lean_ctor_get(v___y_638_, 7);
                v_env_643_ = crate::leanh::lean_ctor_get(v___x_640_, 0);
                v_nextMacroScope_644_ = crate::leanh::lean_ctor_get(v___x_640_, 1);
                v_ngen_645_ = crate::leanh::lean_ctor_get(v___x_640_, 2);
                v_auxDeclNGen_646_ = crate::leanh::lean_ctor_get(v___x_640_, 3);
                v_traceState_647_ = crate::leanh::lean_ctor_get(v___x_640_, 4);
                v_cache_648_ = crate::leanh::lean_ctor_get(v___x_640_, 5);
                v_messages_649_ = crate::leanh::lean_ctor_get(v___x_640_, 6);
                v_infoState_650_ = crate::leanh::lean_ctor_get(v___x_640_, 7);
                v_snapshotTasks_651_ = crate::leanh::lean_ctor_get(v___x_640_, 8);
                v_isSharedCheck_665_ = (!crate::leanh::lean_is_exclusive(v___x_640_)) as u8;
                if v_isSharedCheck_665_ == 0 {
                    v___x_653_ = v___x_640_;
                    v_isShared_654_ = v_isSharedCheck_665_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_651_);
                    crate::leanh::lean_inc(v_infoState_650_);
                    crate::leanh::lean_inc(v_messages_649_);
                    crate::leanh::lean_inc(v_cache_648_);
                    crate::leanh::lean_inc(v_traceState_647_);
                    crate::leanh::lean_inc(v_auxDeclNGen_646_);
                    crate::leanh::lean_inc(v_ngen_645_);
                    crate::leanh::lean_inc(v_nextMacroScope_644_);
                    crate::leanh::lean_inc(v_env_643_);
                    crate::leanh::lean_dec(v___x_640_);
                    v___x_653_ = crate::leanh::lean_box(0);
                    v_isShared_654_ = v_isSharedCheck_665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_642_);
                crate::leanh::lean_inc(v_currNamespace_641_);
                v___x_655_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_655_, 0, v_currNamespace_641_);
                crate::leanh::lean_ctor_set(v___x_655_, 1, v_openDecls_642_);
                v___x_656_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_656_, 0, v___x_655_);
                crate::leanh::lean_ctor_set(v___x_656_, 1, v___y_633_);
                crate::leanh::lean_inc_ref(v___y_637_);
                crate::leanh::lean_inc_ref(v___y_635_);
                v___x_657_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_657_, 0, v___y_635_);
                crate::leanh::lean_ctor_set(v___x_657_, 1, v___y_632_);
                crate::leanh::lean_ctor_set(v___x_657_, 2, v___y_634_);
                crate::leanh::lean_ctor_set(v___x_657_, 3, v___y_637_);
                crate::leanh::lean_ctor_set(v___x_657_, 4, v___x_656_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_657_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_631_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_657_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_636_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_657_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_626_,
                );
                v___x_658_ = l_Lean_MessageLog_add(v___x_657_, v_messages_649_);
                if v_isShared_654_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_653_, 6, v___x_658_);
                    v___x_660_ = v___x_653_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 0, v_env_643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 1, v_nextMacroScope_644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 2, v_ngen_645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 3, v_auxDeclNGen_646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 4, v_traceState_647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 5, v_cache_648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 6, v___x_658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 7, v_infoState_650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 8, v_snapshotTasks_651_);
                    v___x_660_ = v_reuseFailAlloc_664_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_661_ = lean_st_ref_set(v___y_639_, v___x_660_);
                v___x_662_ = crate::leanh::lean_box(0);
                v___x_663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_663_, 0, v___x_662_);
                return v___x_663_;
            }
            4 => {
                v___x_675_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_624_,
                    );
                v___x_676_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v___x_675_, v___y_627_, v___y_628_);
                v_a_677_ = crate::leanh::lean_ctor_get(v___x_676_, 0);
                v_isSharedCheck_690_ = (!crate::leanh::lean_is_exclusive(v___x_676_)) as u8;
                if v_isSharedCheck_690_ == 0 {
                    v___x_679_ = v___x_676_;
                    v_isShared_680_ = v_isSharedCheck_690_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_677_);
                    crate::leanh::lean_dec(v___x_676_);
                    v___x_679_ = crate::leanh::lean_box(0);
                    v_isShared_680_ = v_isSharedCheck_690_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_670_, 2);
                v___x_681_ = l_Lean_FileMap_toPosition(v___y_670_, v___y_669_);
                crate::leanh::lean_dec(v___y_669_);
                v___x_682_ = l_Lean_FileMap_toPosition(v___y_670_, v___y_674_);
                crate::leanh::lean_dec(v___y_674_);
                v___x_683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_683_, 0, v___x_682_);
                v___x_684_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0;
                if v___y_672_ == 0 {
                    crate::leanh::lean_del_object(v___x_679_);
                    crate::leanh::lean_dec_ref(v___y_667_);
                    v___y_631_ = v___y_668_;
                    v___y_632_ = v___x_681_;
                    v___y_633_ = v_a_677_;
                    v___y_634_ = v___x_683_;
                    v___y_635_ = v___y_671_;
                    v___y_636_ = v___y_673_;
                    v___y_637_ = v___x_684_;
                    v___y_638_ = v___y_627_;
                    v___y_639_ = v___y_628_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_677_);
                    v___x_685_ = l_Lean_MessageData_hasTag(v___y_667_, v_a_677_);
                    if v___x_685_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_683_, 1);
                        crate::leanh::lean_dec_ref(v___x_681_);
                        crate::leanh::lean_dec(v_a_677_);
                        v___x_686_ = crate::leanh::lean_box(0);
                        if v_isShared_680_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_679_, 0, v___x_686_);
                            v___x_688_ = v___x_679_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
                            v___x_688_ = v_reuseFailAlloc_689_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_679_);
                        v___y_631_ = v___y_668_;
                        v___y_632_ = v___x_681_;
                        v___y_633_ = v_a_677_;
                        v___y_634_ = v___x_683_;
                        v___y_635_ = v___y_671_;
                        v___y_636_ = v___y_673_;
                        v___y_637_ = v___x_684_;
                        v___y_638_ = v___y_627_;
                        v___y_639_ = v___y_628_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_688_;
            }
            7 => {
                v___x_700_ = l_Lean_Syntax_getTailPos_x3f(v___y_696_, v___y_693_);
                crate::leanh::lean_dec(v___y_696_);
                if crate::leanh::lean_obj_tag(v___x_700_) == 0 {
                    crate::leanh::lean_inc(v___y_699_);
                    v___y_667_ = v___y_692_;
                    v___y_668_ = v___y_693_;
                    v___y_669_ = v___y_699_;
                    v___y_670_ = v___y_694_;
                    v___y_671_ = v___y_695_;
                    v___y_672_ = v___y_698_;
                    v___y_673_ = v___y_697_;
                    v___y_674_ = v___y_699_;
                    state = 4;
                    continue;
                } else {
                    v_val_701_ = crate::leanh::lean_ctor_get(v___x_700_, 0);
                    crate::leanh::lean_inc(v_val_701_);
                    crate::leanh::lean_dec_ref_known(v___x_700_, 1);
                    v___y_667_ = v___y_692_;
                    v___y_668_ = v___y_693_;
                    v___y_669_ = v___y_699_;
                    v___y_670_ = v___y_694_;
                    v___y_671_ = v___y_695_;
                    v___y_672_ = v___y_698_;
                    v___y_673_ = v___y_697_;
                    v___y_674_ = v_val_701_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_710_ = l_Lean_replaceRef(v_ref_623_, v___y_705_);
                v___x_711_ = l_Lean_Syntax_getPos_x3f(v_ref_710_, v___y_704_);
                if crate::leanh::lean_obj_tag(v___x_711_) == 0 {
                    v___x_712_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_692_ = v___y_703_;
                    v___y_693_ = v___y_704_;
                    v___y_694_ = v___y_706_;
                    v___y_695_ = v___y_707_;
                    v___y_696_ = v_ref_710_;
                    v___y_697_ = v___y_709_;
                    v___y_698_ = v___y_708_;
                    v___y_699_ = v___x_712_;
                    state = 7;
                    continue;
                } else {
                    v_val_713_ = crate::leanh::lean_ctor_get(v___x_711_, 0);
                    crate::leanh::lean_inc(v_val_713_);
                    crate::leanh::lean_dec_ref_known(v___x_711_, 1);
                    v___y_692_ = v___y_703_;
                    v___y_693_ = v___y_704_;
                    v___y_694_ = v___y_706_;
                    v___y_695_ = v___y_707_;
                    v___y_696_ = v_ref_710_;
                    v___y_697_ = v___y_709_;
                    v___y_698_ = v___y_708_;
                    v___y_699_ = v_val_713_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_722_ == 0 {
                    v___y_703_ = v___y_717_;
                    v___y_704_ = v___y_721_;
                    v___y_705_ = v___y_716_;
                    v___y_706_ = v___y_718_;
                    v___y_707_ = v___y_719_;
                    v___y_708_ = v___y_720_;
                    v___y_709_ = v_severity_625_;
                    state = 8;
                    continue;
                } else {
                    v___y_703_ = v___y_717_;
                    v___y_704_ = v___y_721_;
                    v___y_705_ = v___y_716_;
                    v___y_706_ = v___y_718_;
                    v___y_707_ = v___y_719_;
                    v___y_708_ = v___y_720_;
                    v___y_709_ = v___x_714_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_724_ == 0 {
                    v_fileName_725_ = crate::leanh::lean_ctor_get(v___y_627_, 0);
                    v_fileMap_726_ = crate::leanh::lean_ctor_get(v___y_627_, 1);
                    v_options_727_ = crate::leanh::lean_ctor_get(v___y_627_, 2);
                    v_ref_728_ = crate::leanh::lean_ctor_get(v___y_627_, 5);
                    v_suppressElabErrors_729_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_627_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_730_ = crate::leanh::lean_box((v___y_724_) as usize);
                    v___x_731_ = crate::leanh::lean_box((v_suppressElabErrors_729_) as usize);
                    v___f_732_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_732_, 0, v___x_730_);
                    crate::leanh::lean_closure_set(v___f_732_, 1, v___x_731_);
                    v___x_733_ = 1;
                    v___x_734_ = l_Lean_instBEqMessageSeverity_beq(v_severity_625_, v___x_733_);
                    if v___x_734_ == 0 {
                        v___y_716_ = v_ref_728_;
                        v___y_717_ = v___f_732_;
                        v___y_718_ = v_fileMap_726_;
                        v___y_719_ = v_fileName_725_;
                        v___y_720_ = v_suppressElabErrors_729_;
                        v___y_721_ = v___y_724_;
                        v___y_722_ = v___x_734_;
                        state = 9;
                        continue;
                    } else {
                        v___x_735_ = l_Lean_warningAsError;
                        v___x_736_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_options_727_, v___x_735_);
                        v___y_716_ = v_ref_728_;
                        v___y_717_ = v___f_732_;
                        v___y_718_ = v_fileMap_726_;
                        v___y_719_ = v_fileName_725_;
                        v___y_720_ = v_suppressElabErrors_729_;
                        v___y_721_ = v___y_724_;
                        v___y_722_ = v___x_736_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_624_);
                    v___x_737_ = crate::leanh::lean_box(0);
                    v___x_738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
                    return v___x_738_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(
    mut v_ref_741_: *mut crate::leanh::LeanObject,
    mut v_msgData_742_: *mut crate::leanh::LeanObject,
    mut v_severity_743_: *mut crate::leanh::LeanObject,
    mut v_isSilent_744_: *mut crate::leanh::LeanObject,
    mut v___y_745_: *mut crate::leanh::LeanObject,
    mut v___y_746_: *mut crate::leanh::LeanObject,
    mut v___y_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_748_: u8 = 0;
    let mut v_isSilent_boxed_749_: u8 = 0;
    let mut v_res_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_748_ = (crate::leanh::lean_unbox(v_severity_743_) as u8);
    v_isSilent_boxed_749_ = (crate::leanh::lean_unbox(v_isSilent_744_) as u8);
    v_res_750_ =
        l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(
            v_ref_741_,
            v_msgData_742_,
            v_severity_boxed_748_,
            v_isSilent_boxed_749_,
            v___y_745_,
            v___y_746_,
        );
    crate::leanh::lean_dec(v___y_746_);
    crate::leanh::lean_dec_ref(v___y_745_);
    crate::leanh::lean_dec(v_ref_741_);
    return v_res_750_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(
    mut v_ref_751_: *mut crate::leanh::LeanObject,
    mut v_msgData_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_756_: u8 = 0;
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = 0;
    v___x_757_ = 0;
    v___x_758_ =
        l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(
            v_ref_751_,
            v_msgData_752_,
            v___x_756_,
            v___x_757_,
            v___y_753_,
            v___y_754_,
        );
    return v___x_758_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0___boxed(
    mut v_ref_759_: *mut crate::leanh::LeanObject,
    mut v_msgData_760_: *mut crate::leanh::LeanObject,
    mut v___y_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_764_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(
        v_ref_759_,
        v_msgData_760_,
        v___y_761_,
        v___y_762_,
    );
    crate::leanh::lean_dec(v___y_762_);
    crate::leanh::lean_dec_ref(v___y_761_);
    crate::leanh::lean_dec(v_ref_759_);
    return v_res_764_;
}
pub unsafe fn l_Lean_reportOutOfHeartbeats(
    mut v_tac_767_: *mut crate::leanh::LeanObject,
    mut v_stx_768_: *mut crate::leanh::LeanObject,
    mut v_threshold_769_: *mut crate::leanh::LeanObject,
    mut v_a_770_: *mut crate::leanh::LeanObject,
    mut v_a_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_777_: u8 = 0;
    let mut v___x_778_: u8 = 0;
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_773_ = l_Lean_heartbeatsPercent___redArg(v_a_770_);
                v_a_774_ = crate::leanh::lean_ctor_get(v___x_773_, 0);
                v_isSharedCheck_791_ = (!crate::leanh::lean_is_exclusive(v___x_773_)) as u8;
                if v_isSharedCheck_791_ == 0 {
                    v___x_776_ = v___x_773_;
                    v_isShared_777_ = v_isSharedCheck_791_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_774_);
                    crate::leanh::lean_dec(v___x_773_);
                    v___x_776_ = crate::leanh::lean_box(0);
                    v_isShared_777_ = v_isSharedCheck_791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_778_ = lean_nat_dec_le(v_threshold_769_, v_a_774_);
                crate::leanh::lean_dec(v_a_774_);
                if v___x_778_ == 0 {
                    crate::leanh::lean_dec(v_tac_767_);
                    v___x_779_ = crate::leanh::lean_box(0);
                    if v_isShared_777_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_776_, 0, v___x_779_);
                        v___x_781_ = v___x_776_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                        v___x_781_ = v_reuseFailAlloc_782_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_776_);
                    v___x_783_ = l_Lean_reportOutOfHeartbeats___closed__0;
                    v___x_784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_tac_767_, v___x_778_,
                    );
                    v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
                    crate::leanh::lean_dec_ref(v___x_784_);
                    v___x_786_ = l_Lean_reportOutOfHeartbeats___closed__1;
                    v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
                    v___x_788_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_788_, 0, v___x_787_);
                    v___x_789_ = l_Lean_MessageData_ofFormat(v___x_788_);
                    v___x_790_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(
                        v_stx_768_, v___x_789_, v_a_770_, v_a_771_,
                    );
                    return v___x_790_;
                }
            }
            2 => {
                return v___x_781_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_reportOutOfHeartbeats___boxed(
    mut v_tac_792_: *mut crate::leanh::LeanObject,
    mut v_stx_793_: *mut crate::leanh::LeanObject,
    mut v_threshold_794_: *mut crate::leanh::LeanObject,
    mut v_a_795_: *mut crate::leanh::LeanObject,
    mut v_a_796_: *mut crate::leanh::LeanObject,
    mut v_a_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ =
        l_Lean_reportOutOfHeartbeats(v_tac_792_, v_stx_793_, v_threshold_794_, v_a_795_, v_a_796_);
    crate::leanh::lean_dec(v_a_796_);
    crate::leanh::lean_dec_ref(v_a_795_);
    crate::leanh::lean_dec(v_threshold_794_);
    crate::leanh::lean_dec(v_stx_793_);
    return v_res_798_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Heartbeats(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Heartbeats(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Heartbeats(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Heartbeats(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Heartbeats(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_Heartbeats(builtin);
}
