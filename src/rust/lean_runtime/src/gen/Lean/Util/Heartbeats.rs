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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lean_withHeartbeats___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_IO_getNumHeartbeats___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_withHeartbeats___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_withHeartbeats___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_reportOutOfHeartbeats___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_reportOutOfHeartbeats___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_reportOutOfHeartbeats___closed__0_value) as *mut LeanObject;
pub static l_Lean_reportOutOfHeartbeats___closed__1_value: LeanStringObject<109> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_reportOutOfHeartbeats___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_reportOutOfHeartbeats___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__0(
    mut v_start_400_: *mut LeanObject,
    mut v_r_401_: *mut LeanObject,
    mut v_toPure_402_: *mut LeanObject,
    mut v_finish_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    v___x_404_ = lean_nat_sub(v_finish_403_, v_start_400_);
    v___x_405_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_405_, 0, v_r_401_);
    lean_ctor_set(v___x_405_, 1, v___x_404_);
    v___x_406_ = lean_apply_2(v_toPure_402_, lean_box(0), v___x_405_);
    return v___x_406_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__0___boxed(
    mut v_start_407_: *mut LeanObject,
    mut v_r_408_: *mut LeanObject,
    mut v_toPure_409_: *mut LeanObject,
    mut v_finish_410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_411_: *mut LeanObject = core::ptr::null_mut();
    v_res_411_ = l_Lean_withHeartbeats___redArg___lam__0(
        v_start_407_,
        v_r_408_,
        v_toPure_409_,
        v_finish_410_,
    );
    lean_dec(v_finish_410_);
    lean_dec(v_start_407_);
    return v_res_411_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__1(
    mut v_start_412_: *mut LeanObject,
    mut v_toPure_413_: *mut LeanObject,
    mut v_toBind_414_: *mut LeanObject,
    mut v___x_415_: *mut LeanObject,
    mut v_r_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    v___f_417_ = lean_alloc_closure(
        l_Lean_withHeartbeats___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_417_, 0, v_start_412_);
    lean_closure_set(v___f_417_, 1, v_r_416_);
    lean_closure_set(v___f_417_, 2, v_toPure_413_);
    v___x_418_ = lean_apply_4(
        v_toBind_414_,
        lean_box(0),
        lean_box(0),
        v___x_415_,
        v___f_417_,
    );
    return v___x_418_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg___lam__2(
    mut v_toPure_419_: *mut LeanObject,
    mut v_toBind_420_: *mut LeanObject,
    mut v___x_421_: *mut LeanObject,
    mut v_x_422_: *mut LeanObject,
    mut v_start_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_toBind_420_);
    v___f_424_ = lean_alloc_closure(
        l_Lean_withHeartbeats___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_424_, 0, v_start_423_);
    lean_closure_set(v___f_424_, 1, v_toPure_419_);
    lean_closure_set(v___f_424_, 2, v_toBind_420_);
    lean_closure_set(v___f_424_, 3, v___x_421_);
    v___x_425_ = lean_apply_4(
        v_toBind_420_,
        lean_box(0),
        lean_box(0),
        v_x_422_,
        v___f_424_,
    );
    return v___x_425_;
}
pub unsafe fn l_Lean_withHeartbeats___redArg(
    mut v_inst_427_: *mut LeanObject,
    mut v_inst_428_: *mut LeanObject,
    mut v_x_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_430_ = lean_ctor_get(v_inst_427_, 0);
    lean_inc_ref(v_toApplicative_430_);
    v_toBind_431_ = lean_ctor_get(v_inst_427_, 1);
    lean_inc_n(v_toBind_431_, 2);
    lean_dec_ref(v_inst_427_);
    v_toPure_432_ = lean_ctor_get(v_toApplicative_430_, 1);
    lean_inc(v_toPure_432_);
    lean_dec_ref(v_toApplicative_430_);
    v___x_433_ = l_Lean_withHeartbeats___redArg___closed__0;
    v___x_434_ = lean_apply_2(v_inst_428_, lean_box(0), v___x_433_);
    lean_inc(v___x_434_);
    v___f_435_ = lean_alloc_closure(
        l_Lean_withHeartbeats___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_435_, 0, v_toPure_432_);
    lean_closure_set(v___f_435_, 1, v_toBind_431_);
    lean_closure_set(v___f_435_, 2, v___x_434_);
    lean_closure_set(v___f_435_, 3, v_x_429_);
    v___x_436_ = lean_apply_4(
        v_toBind_431_,
        lean_box(0),
        lean_box(0),
        v___x_434_,
        v___f_435_,
    );
    return v___x_436_;
}
pub unsafe fn l_Lean_withHeartbeats(
    mut v_m_437_: *mut LeanObject,
    mut v_00_u03b1_438_: *mut LeanObject,
    mut v_inst_439_: *mut LeanObject,
    mut v_inst_440_: *mut LeanObject,
    mut v_x_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    v___x_442_ = l_Lean_withHeartbeats___redArg(v_inst_439_, v_inst_440_, v_x_441_);
    return v___x_442_;
}
pub unsafe fn l_Lean_getMaxHeartbeats___redArg(mut v_a_443_: *mut LeanObject) -> *mut LeanObject {
    let mut v_maxHeartbeats_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    v_maxHeartbeats_445_ = lean_ctor_get(v_a_443_, 9);
    lean_inc(v_maxHeartbeats_445_);
    v___x_446_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_446_, 0, v_maxHeartbeats_445_);
    return v___x_446_;
}
pub unsafe fn l_Lean_getMaxHeartbeats___redArg___boxed(
    mut v_a_447_: *mut LeanObject,
    mut v_a_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Lean_getMaxHeartbeats___redArg(v_a_447_);
    lean_dec_ref(v_a_447_);
    return v_res_449_;
}
pub unsafe fn l_Lean_getMaxHeartbeats(
    mut v_a_450_: *mut LeanObject,
    mut v_a_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    v___x_453_ = l_Lean_getMaxHeartbeats___redArg(v_a_450_);
    return v___x_453_;
}
pub unsafe fn l_Lean_getMaxHeartbeats___boxed(
    mut v_a_454_: *mut LeanObject,
    mut v_a_455_: *mut LeanObject,
    mut v_a_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_457_: *mut LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Lean_getMaxHeartbeats(v_a_454_, v_a_455_);
    lean_dec(v_a_455_);
    lean_dec_ref(v_a_454_);
    return v_res_457_;
}
pub unsafe fn l_Lean_getInitHeartbeats___redArg(mut v_a_458_: *mut LeanObject) -> *mut LeanObject {
    let mut v_initHeartbeats_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v_initHeartbeats_460_ = lean_ctor_get(v_a_458_, 8);
    lean_inc(v_initHeartbeats_460_);
    v___x_461_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_461_, 0, v_initHeartbeats_460_);
    return v___x_461_;
}
pub unsafe fn l_Lean_getInitHeartbeats___redArg___boxed(
    mut v_a_462_: *mut LeanObject,
    mut v_a_463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_464_: *mut LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Lean_getInitHeartbeats___redArg(v_a_462_);
    lean_dec_ref(v_a_462_);
    return v_res_464_;
}
pub unsafe fn l_Lean_getInitHeartbeats(
    mut v_a_465_: *mut LeanObject,
    mut v_a_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    v___x_468_ = l_Lean_getInitHeartbeats___redArg(v_a_465_);
    return v___x_468_;
}
pub unsafe fn l_Lean_getInitHeartbeats___boxed(
    mut v_a_469_: *mut LeanObject,
    mut v_a_470_: *mut LeanObject,
    mut v_a_471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_472_: *mut LeanObject = core::ptr::null_mut();
    v_res_472_ = l_Lean_getInitHeartbeats(v_a_469_, v_a_470_);
    lean_dec(v_a_470_);
    lean_dec_ref(v_a_469_);
    return v_res_472_;
}
pub unsafe fn l_Lean_getRemainingHeartbeats___redArg(
    mut v_a_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_475_ = l_Lean_getMaxHeartbeats___redArg(v_a_473_);
                v_a_476_ = lean_ctor_get(v___x_475_, 0);
                lean_inc(v_a_476_);
                lean_dec_ref(v___x_475_);
                v___x_477_ = lean_io_get_num_heartbeats();
                v___x_478_ = l_Lean_getInitHeartbeats___redArg(v_a_473_);
                v_a_479_ = lean_ctor_get(v___x_478_, 0);
                v_isSharedCheck_488_ = (!lean_is_exclusive(v___x_478_)) as u8;
                if v_isSharedCheck_488_ == 0 {
                    v___x_481_ = v___x_478_;
                    v_isShared_482_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_479_);
                    lean_dec(v___x_478_);
                    v___x_481_ = lean_box(0);
                    v_isShared_482_ = v_isSharedCheck_488_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_483_ = lean_nat_sub(v___x_477_, v_a_479_);
                lean_dec(v_a_479_);
                lean_dec(v___x_477_);
                v___x_484_ = lean_nat_sub(v_a_476_, v___x_483_);
                lean_dec(v___x_483_);
                lean_dec(v_a_476_);
                if v_isShared_482_ == 0 {
                    lean_ctor_set(v___x_481_, 0, v___x_484_);
                    v___x_486_ = v___x_481_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
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
    mut v_a_489_: *mut LeanObject,
    mut v_a_490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_491_: *mut LeanObject = core::ptr::null_mut();
    v_res_491_ = l_Lean_getRemainingHeartbeats___redArg(v_a_489_);
    lean_dec_ref(v_a_489_);
    return v_res_491_;
}
pub unsafe fn l_Lean_getRemainingHeartbeats(
    mut v_a_492_: *mut LeanObject,
    mut v_a_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    v___x_495_ = l_Lean_getRemainingHeartbeats___redArg(v_a_492_);
    return v___x_495_;
}
pub unsafe fn l_Lean_getRemainingHeartbeats___boxed(
    mut v_a_496_: *mut LeanObject,
    mut v_a_497_: *mut LeanObject,
    mut v_a_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_499_: *mut LeanObject = core::ptr::null_mut();
    v_res_499_ = l_Lean_getRemainingHeartbeats(v_a_496_, v_a_497_);
    lean_dec(v_a_497_);
    lean_dec_ref(v_a_496_);
    return v_res_499_;
}
pub unsafe fn l_Lean_heartbeatsPercent___redArg(mut v_a_500_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_509_: u8 = 0;
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_502_ = lean_io_get_num_heartbeats();
                v___x_503_ = l_Lean_getInitHeartbeats___redArg(v_a_500_);
                v_a_504_ = lean_ctor_get(v___x_503_, 0);
                lean_inc(v_a_504_);
                lean_dec_ref(v___x_503_);
                v___x_505_ = l_Lean_getMaxHeartbeats___redArg(v_a_500_);
                v_a_506_ = lean_ctor_get(v___x_505_, 0);
                v_isSharedCheck_517_ = (!lean_is_exclusive(v___x_505_)) as u8;
                if v_isSharedCheck_517_ == 0 {
                    v___x_508_ = v___x_505_;
                    v_isShared_509_ = v_isSharedCheck_517_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_506_);
                    lean_dec(v___x_505_);
                    v___x_508_ = lean_box(0);
                    v_isShared_509_ = v_isSharedCheck_517_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_510_ = lean_nat_sub(v___x_502_, v_a_504_);
                lean_dec(v_a_504_);
                lean_dec(v___x_502_);
                v___x_511_ = lean_unsigned_to_nat(100);
                v___x_512_ = lean_nat_mul(v___x_510_, v___x_511_);
                lean_dec(v___x_510_);
                v___x_513_ = lean_nat_div(v___x_512_, v_a_506_);
                lean_dec(v_a_506_);
                lean_dec(v___x_512_);
                if v_isShared_509_ == 0 {
                    lean_ctor_set(v___x_508_, 0, v___x_513_);
                    v___x_515_ = v___x_508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
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
    mut v_a_518_: *mut LeanObject,
    mut v_a_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_520_: *mut LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Lean_heartbeatsPercent___redArg(v_a_518_);
    lean_dec_ref(v_a_518_);
    return v_res_520_;
}
pub unsafe fn l_Lean_heartbeatsPercent(
    mut v_a_521_: *mut LeanObject,
    mut v_a_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_heartbeatsPercent___redArg(v_a_521_);
    return v___x_524_;
}
pub unsafe fn l_Lean_heartbeatsPercent___boxed(
    mut v_a_525_: *mut LeanObject,
    mut v_a_526_: *mut LeanObject,
    mut v_a_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_528_: *mut LeanObject = core::ptr::null_mut();
    v_res_528_ = l_Lean_heartbeatsPercent(v_a_525_, v_a_526_);
    lean_dec(v_a_526_);
    lean_dec_ref(v_a_525_);
    return v_res_528_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(
    mut v___y_537_: u8,
    mut v_suppressElabErrors_538_: u8,
    mut v_x_539_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_539_) == 1 {
        let mut v_pre_540_: *mut LeanObject = core::ptr::null_mut();
        v_pre_540_ = lean_ctor_get(v_x_539_, 0);
        match lean_obj_tag(v_pre_540_) {
            1 => {
                let mut v_pre_541_: *mut LeanObject = core::ptr::null_mut();
                v_pre_541_ = lean_ctor_get(v_pre_540_, 0);
                match lean_obj_tag(v_pre_541_) {
                    0 => {
                        let mut v_str_542_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_543_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_545_: u8 = 0;
                        v_str_542_ = lean_ctor_get(v_x_539_, 1);
                        v_str_543_ = lean_ctor_get(v_pre_540_, 1);
                        v___x_544_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__0;
                        v___x_545_ = lean_string_dec_eq(v_str_543_, v___x_544_);
                        if v___x_545_ == 0 {
                            let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_547_: u8 = 0;
                            v___x_546_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__1;
                            v___x_547_ = lean_string_dec_eq(v_str_543_, v___x_546_);
                            if v___x_547_ == 0 {
                                return v___y_537_;
                            } else {
                                let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_552_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_552_ = lean_ctor_get(v_pre_541_, 0);
                        if lean_obj_tag(v_pre_552_) == 0 {
                            let mut v_str_553_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_554_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_555_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_557_: u8 = 0;
                            v_str_553_ = lean_ctor_get(v_x_539_, 1);
                            v_str_554_ = lean_ctor_get(v_pre_540_, 1);
                            v_str_555_ = lean_ctor_get(v_pre_541_, 1);
                            v___x_556_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__4;
                            v___x_557_ = lean_string_dec_eq(v_str_555_, v___x_556_);
                            if v___x_557_ == 0 {
                                return v___y_537_;
                            } else {
                                let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_559_: u8 = 0;
                                v___x_558_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___closed__5;
                                v___x_559_ = lean_string_dec_eq(v_str_554_, v___x_558_);
                                if v___x_559_ == 0 {
                                    return v___y_537_;
                                } else {
                                    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_562_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_564_: u8 = 0;
                v_str_562_ = lean_ctor_get(v_x_539_, 1);
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
    mut v___y_565_: *mut LeanObject,
    mut v_suppressElabErrors_566_: *mut LeanObject,
    mut v_x_567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2452__boxed_568_: u8 = 0;
    let mut v_suppressElabErrors_boxed_569_: u8 = 0;
    let mut v_res_570_: u8 = 0;
    let mut v_r_571_: *mut LeanObject = core::ptr::null_mut();
    v___y_2452__boxed_568_ = (lean_unbox(v___y_565_) as u8);
    v_suppressElabErrors_boxed_569_ = (lean_unbox(v_suppressElabErrors_566_) as u8);
    v_res_570_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0(v___y_2452__boxed_568_, v_suppressElabErrors_boxed_569_, v_x_567_);
    lean_dec(v_x_567_);
    v_r_571_ = lean_box((v_res_570_) as usize);
    return v_r_571_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(
    mut v_opts_572_: *mut LeanObject,
    mut v_opt_573_: *mut LeanObject,
) -> u8 {
    let mut v_name_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    v_name_574_ = lean_ctor_get(v_opt_573_, 0);
    v_defValue_575_ = lean_ctor_get(v_opt_573_, 1);
    v_map_576_ = lean_ctor_get(v_opts_572_, 0);
    v___x_577_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_576_,
            v_name_574_,
        );
    if lean_obj_tag(v___x_577_) == 0 {
        let mut v___x_578_: u8 = 0;
        v___x_578_ = (lean_unbox(v_defValue_575_) as u8);
        return v___x_578_;
    } else {
        let mut v_val_579_: *mut LeanObject = core::ptr::null_mut();
        v_val_579_ = lean_ctor_get(v___x_577_, 0);
        lean_inc(v_val_579_);
        lean_dec_ref_known(v___x_577_, 1);
        if lean_obj_tag(v_val_579_) == 1 {
            let mut v_v_580_: u8 = 0;
            v_v_580_ = lean_ctor_get_uint8(v_val_579_, 0 as u32);
            lean_dec_ref_known(v_val_579_, 0);
            return v_v_580_;
        } else {
            let mut v___x_581_: u8 = 0;
            lean_dec(v_val_579_);
            v___x_581_ = (lean_unbox(v_defValue_575_) as u8);
            return v___x_581_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2___boxed(
    mut v_opts_582_: *mut LeanObject,
    mut v_opt_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_584_: u8 = 0;
    let mut v_r_585_: *mut LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__2(v_opts_582_, v_opt_583_);
    lean_dec_ref(v_opt_583_);
    lean_dec_ref(v_opts_582_);
    v_r_585_ = lean_box((v_res_584_) as usize);
    return v_r_585_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    v___x_586_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_586_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    v___x_587_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__0);
    v___x_588_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_588_, 0, v___x_587_);
    return v___x_588_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    v___x_589_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
    v___x_590_ = lean_unsigned_to_nat(0);
    v___x_591_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_591_, 0, v___x_590_);
    lean_ctor_set(v___x_591_, 1, v___x_590_);
    lean_ctor_set(v___x_591_, 2, v___x_590_);
    lean_ctor_set(v___x_591_, 3, v___x_590_);
    lean_ctor_set(v___x_591_, 4, v___x_589_);
    lean_ctor_set(v___x_591_, 5, v___x_589_);
    lean_ctor_set(v___x_591_, 6, v___x_589_);
    lean_ctor_set(v___x_591_, 7, v___x_589_);
    lean_ctor_set(v___x_591_, 8, v___x_589_);
    lean_ctor_set(v___x_591_, 9, v___x_589_);
    return v___x_591_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = lean_unsigned_to_nat(32);
    v___x_593_ = lean_mk_empty_array_with_capacity(v___x_592_);
    v___x_594_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_594_, 0, v___x_593_);
    return v___x_594_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_595_: usize = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = 5usize;
    v___x_596_ = lean_unsigned_to_nat(0);
    v___x_597_ = lean_unsigned_to_nat(32);
    v___x_598_ = lean_mk_empty_array_with_capacity(v___x_597_);
    v___x_599_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__3);
    v___x_600_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_600_, 0, v___x_599_);
    lean_ctor_set(v___x_600_, 1, v___x_598_);
    lean_ctor_set(v___x_600_, 2, v___x_596_);
    lean_ctor_set(v___x_600_, 3, v___x_596_);
    lean_ctor_set_usize(v___x_600_, 4, v___x_595_);
    return v___x_600_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    v___x_601_ = lean_box(1);
    v___x_602_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__4);
    v___x_603_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__1);
    v___x_604_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_604_, 0, v___x_603_);
    lean_ctor_set(v___x_604_, 1, v___x_602_);
    lean_ctor_set(v___x_604_, 2, v___x_601_);
    return v___x_604_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(
    mut v_msgData_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
    mut v___y_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    v___x_609_ = lean_st_ref_get(v___y_607_);
    v_env_610_ = lean_ctor_get(v___x_609_, 0);
    lean_inc_ref(v_env_610_);
    lean_dec(v___x_609_);
    v_options_611_ = lean_ctor_get(v___y_606_, 2);
    v___x_612_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__2);
    v___x_613_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___closed__5);
    lean_inc_ref(v_options_611_);
    v___x_614_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_614_, 0, v_env_610_);
    lean_ctor_set(v___x_614_, 1, v___x_612_);
    lean_ctor_set(v___x_614_, 2, v___x_613_);
    lean_ctor_set(v___x_614_, 3, v_options_611_);
    v___x_615_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_615_, 0, v___x_614_);
    lean_ctor_set(v___x_615_, 1, v_msgData_605_);
    v___x_616_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_616_, 0, v___x_615_);
    return v___x_616_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_617_: *mut LeanObject,
    mut v___y_618_: *mut LeanObject,
    mut v___y_619_: *mut LeanObject,
    mut v___y_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_621_: *mut LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v_msgData_617_, v___y_618_, v___y_619_);
    lean_dec(v___y_619_);
    lean_dec_ref(v___y_618_);
    return v_res_621_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(
    mut v_ref_623_: *mut LeanObject,
    mut v_msgData_624_: *mut LeanObject,
    mut v_severity_625_: u8,
    mut v_isSilent_626_: u8,
    mut v___y_627_: *mut LeanObject,
    mut v___y_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_631_: u8 = 0;
    let mut v___y_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_636_: u8 = 0;
    let mut v___y_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_654_: u8 = 0;
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut v___y_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_668_: u8 = 0;
    let mut v___y_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_672_: u8 = 0;
    let mut v___y_673_: u8 = 0;
    let mut v___y_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_680_: u8 = 0;
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut v___y_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_693_: u8 = 0;
    let mut v___y_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_697_: u8 = 0;
    let mut v___y_698_: u8 = 0;
    let mut v___y_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_704_: u8 = 0;
    let mut v___y_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_708_: u8 = 0;
    let mut v___y_709_: u8 = 0;
    let mut v_ref_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v___y_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_720_: u8 = 0;
    let mut v___y_721_: u8 = 0;
    let mut v___y_722_: u8 = 0;
    let mut v___y_724_: u8 = 0;
    let mut v_fileName_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_729_: u8 = 0;
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: u8 = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_624_);
                    v___x_740_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_624_);
                    v___y_724_ = v___x_740_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_640_ = lean_st_ref_take(v___y_639_);
                v_currNamespace_641_ = lean_ctor_get(v___y_638_, 6);
                v_openDecls_642_ = lean_ctor_get(v___y_638_, 7);
                v_env_643_ = lean_ctor_get(v___x_640_, 0);
                v_nextMacroScope_644_ = lean_ctor_get(v___x_640_, 1);
                v_ngen_645_ = lean_ctor_get(v___x_640_, 2);
                v_auxDeclNGen_646_ = lean_ctor_get(v___x_640_, 3);
                v_traceState_647_ = lean_ctor_get(v___x_640_, 4);
                v_cache_648_ = lean_ctor_get(v___x_640_, 5);
                v_messages_649_ = lean_ctor_get(v___x_640_, 6);
                v_infoState_650_ = lean_ctor_get(v___x_640_, 7);
                v_snapshotTasks_651_ = lean_ctor_get(v___x_640_, 8);
                v_isSharedCheck_665_ = (!lean_is_exclusive(v___x_640_)) as u8;
                if v_isSharedCheck_665_ == 0 {
                    v___x_653_ = v___x_640_;
                    v_isShared_654_ = v_isSharedCheck_665_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_651_);
                    lean_inc(v_infoState_650_);
                    lean_inc(v_messages_649_);
                    lean_inc(v_cache_648_);
                    lean_inc(v_traceState_647_);
                    lean_inc(v_auxDeclNGen_646_);
                    lean_inc(v_ngen_645_);
                    lean_inc(v_nextMacroScope_644_);
                    lean_inc(v_env_643_);
                    lean_dec(v___x_640_);
                    v___x_653_ = lean_box(0);
                    v_isShared_654_ = v_isSharedCheck_665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_642_);
                lean_inc(v_currNamespace_641_);
                v___x_655_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_655_, 0, v_currNamespace_641_);
                lean_ctor_set(v___x_655_, 1, v_openDecls_642_);
                v___x_656_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_656_, 0, v___x_655_);
                lean_ctor_set(v___x_656_, 1, v___y_633_);
                lean_inc_ref(v___y_637_);
                lean_inc_ref(v___y_635_);
                v___x_657_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_657_, 0, v___y_635_);
                lean_ctor_set(v___x_657_, 1, v___y_632_);
                lean_ctor_set(v___x_657_, 2, v___y_634_);
                lean_ctor_set(v___x_657_, 3, v___y_637_);
                lean_ctor_set(v___x_657_, 4, v___x_656_);
                lean_ctor_set_uint8(
                    v___x_657_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_631_,
                );
                lean_ctor_set_uint8(
                    v___x_657_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_636_,
                );
                lean_ctor_set_uint8(
                    v___x_657_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_626_,
                );
                v___x_658_ = l_Lean_MessageLog_add(v___x_657_, v_messages_649_);
                if v_isShared_654_ == 0 {
                    lean_ctor_set(v___x_653_, 6, v___x_658_);
                    v___x_660_ = v___x_653_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_664_, 0, v_env_643_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 1, v_nextMacroScope_644_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 2, v_ngen_645_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 3, v_auxDeclNGen_646_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 4, v_traceState_647_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 5, v_cache_648_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 6, v___x_658_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 7, v_infoState_650_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 8, v_snapshotTasks_651_);
                    v___x_660_ = v_reuseFailAlloc_664_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_661_ = lean_st_ref_set(v___y_639_, v___x_660_);
                v___x_662_ = lean_box(0);
                v___x_663_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_663_, 0, v___x_662_);
                return v___x_663_;
            }
            4 => {
                v___x_675_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_624_,
                    );
                v___x_676_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0_spec__1(v___x_675_, v___y_627_, v___y_628_);
                v_a_677_ = lean_ctor_get(v___x_676_, 0);
                v_isSharedCheck_690_ = (!lean_is_exclusive(v___x_676_)) as u8;
                if v_isSharedCheck_690_ == 0 {
                    v___x_679_ = v___x_676_;
                    v_isShared_680_ = v_isSharedCheck_690_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_677_);
                    lean_dec(v___x_676_);
                    v___x_679_ = lean_box(0);
                    v_isShared_680_ = v_isSharedCheck_690_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_670_, 2);
                v___x_681_ = l_Lean_FileMap_toPosition(v___y_670_, v___y_669_);
                lean_dec(v___y_669_);
                v___x_682_ = l_Lean_FileMap_toPosition(v___y_670_, v___y_674_);
                lean_dec(v___y_674_);
                v___x_683_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_683_, 0, v___x_682_);
                v___x_684_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___closed__0;
                if v___y_672_ == 0 {
                    lean_del_object(v___x_679_);
                    lean_dec_ref(v___y_667_);
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
                    lean_inc(v_a_677_);
                    v___x_685_ = l_Lean_MessageData_hasTag(v___y_667_, v_a_677_);
                    if v___x_685_ == 0 {
                        lean_dec_ref_known(v___x_683_, 1);
                        lean_dec_ref(v___x_681_);
                        lean_dec(v_a_677_);
                        v___x_686_ = lean_box(0);
                        if v_isShared_680_ == 0 {
                            lean_ctor_set(v___x_679_, 0, v___x_686_);
                            v___x_688_ = v___x_679_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
                            v___x_688_ = v_reuseFailAlloc_689_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_679_);
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
                lean_dec(v___y_696_);
                if lean_obj_tag(v___x_700_) == 0 {
                    lean_inc(v___y_699_);
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
                    v_val_701_ = lean_ctor_get(v___x_700_, 0);
                    lean_inc(v_val_701_);
                    lean_dec_ref_known(v___x_700_, 1);
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
                if lean_obj_tag(v___x_711_) == 0 {
                    v___x_712_ = lean_unsigned_to_nat(0);
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
                    v_val_713_ = lean_ctor_get(v___x_711_, 0);
                    lean_inc(v_val_713_);
                    lean_dec_ref_known(v___x_711_, 1);
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
                    v_fileName_725_ = lean_ctor_get(v___y_627_, 0);
                    v_fileMap_726_ = lean_ctor_get(v___y_627_, 1);
                    v_options_727_ = lean_ctor_get(v___y_627_, 2);
                    v_ref_728_ = lean_ctor_get(v___y_627_, 5);
                    v_suppressElabErrors_729_ = lean_ctor_get_uint8(
                        v___y_627_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_730_ = lean_box((v___y_724_) as usize);
                    v___x_731_ = lean_box((v_suppressElabErrors_729_) as usize);
                    v___f_732_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_732_, 0, v___x_730_);
                    lean_closure_set(v___f_732_, 1, v___x_731_);
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
                    lean_dec_ref(v_msgData_624_);
                    v___x_737_ = lean_box(0);
                    v___x_738_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_738_, 0, v___x_737_);
                    return v___x_738_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0___boxed(
    mut v_ref_741_: *mut LeanObject,
    mut v_msgData_742_: *mut LeanObject,
    mut v_severity_743_: *mut LeanObject,
    mut v_isSilent_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_748_: u8 = 0;
    let mut v_isSilent_boxed_749_: u8 = 0;
    let mut v_res_750_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_748_ = (lean_unbox(v_severity_743_) as u8);
    v_isSilent_boxed_749_ = (lean_unbox(v_isSilent_744_) as u8);
    v_res_750_ =
        l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0_spec__0(
            v_ref_741_,
            v_msgData_742_,
            v_severity_boxed_748_,
            v_isSilent_boxed_749_,
            v___y_745_,
            v___y_746_,
        );
    lean_dec(v___y_746_);
    lean_dec_ref(v___y_745_);
    lean_dec(v_ref_741_);
    return v_res_750_;
}
pub unsafe fn l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(
    mut v_ref_751_: *mut LeanObject,
    mut v_msgData_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_756_: u8 = 0;
    let mut v___x_757_: u8 = 0;
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_ref_759_: *mut LeanObject,
    mut v_msgData_760_: *mut LeanObject,
    mut v___y_761_: *mut LeanObject,
    mut v___y_762_: *mut LeanObject,
    mut v___y_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_764_: *mut LeanObject = core::ptr::null_mut();
    v_res_764_ = l_Lean_logInfoAt___at___00Lean_reportOutOfHeartbeats_spec__0(
        v_ref_759_,
        v_msgData_760_,
        v___y_761_,
        v___y_762_,
    );
    lean_dec(v___y_762_);
    lean_dec_ref(v___y_761_);
    lean_dec(v_ref_759_);
    return v_res_764_;
}
pub unsafe fn l_Lean_reportOutOfHeartbeats(
    mut v_tac_767_: *mut LeanObject,
    mut v_stx_768_: *mut LeanObject,
    mut v_threshold_769_: *mut LeanObject,
    mut v_a_770_: *mut LeanObject,
    mut v_a_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_777_: u8 = 0;
    let mut v___x_778_: u8 = 0;
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_773_ = l_Lean_heartbeatsPercent___redArg(v_a_770_);
                v_a_774_ = lean_ctor_get(v___x_773_, 0);
                v_isSharedCheck_791_ = (!lean_is_exclusive(v___x_773_)) as u8;
                if v_isSharedCheck_791_ == 0 {
                    v___x_776_ = v___x_773_;
                    v_isShared_777_ = v_isSharedCheck_791_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_774_);
                    lean_dec(v___x_773_);
                    v___x_776_ = lean_box(0);
                    v_isShared_777_ = v_isSharedCheck_791_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_778_ = lean_nat_dec_le(v_threshold_769_, v_a_774_);
                lean_dec(v_a_774_);
                if v___x_778_ == 0 {
                    lean_dec(v_tac_767_);
                    v___x_779_ = lean_box(0);
                    if v_isShared_777_ == 0 {
                        lean_ctor_set(v___x_776_, 0, v___x_779_);
                        v___x_781_ = v___x_776_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                        v___x_781_ = v_reuseFailAlloc_782_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_776_);
                    v___x_783_ = l_Lean_reportOutOfHeartbeats___closed__0;
                    v___x_784_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_tac_767_, v___x_778_,
                    );
                    v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
                    lean_dec_ref(v___x_784_);
                    v___x_786_ = l_Lean_reportOutOfHeartbeats___closed__1;
                    v___x_787_ = lean_string_append(v___x_785_, v___x_786_);
                    v___x_788_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_788_, 0, v___x_787_);
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
    mut v_tac_792_: *mut LeanObject,
    mut v_stx_793_: *mut LeanObject,
    mut v_threshold_794_: *mut LeanObject,
    mut v_a_795_: *mut LeanObject,
    mut v_a_796_: *mut LeanObject,
    mut v_a_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_798_: *mut LeanObject = core::ptr::null_mut();
    v_res_798_ =
        l_Lean_reportOutOfHeartbeats(v_tac_792_, v_stx_793_, v_threshold_794_, v_a_795_, v_a_796_);
    lean_dec(v_a_796_);
    lean_dec_ref(v_a_795_);
    lean_dec(v_threshold_794_);
    lean_dec(v_stx_793_);
    return v_res_798_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_Heartbeats(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_Heartbeats(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_Heartbeats(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_CoreM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Heartbeats(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_Heartbeats(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_Heartbeats(builtin);
}
