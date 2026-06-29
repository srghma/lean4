// Lean compiler output
// Module: Lake.Config.FacetConfig
// Imports: Lake.Build.Fetch
use crate::r#gen::Init::Prelude::l_Lean_mkAtom;
use crate::r#gen::Lake::Build::Fetch::{
    initialize_Lake_Build_Fetch, runtime_initialize_Lake_Build_Fetch,
};
use crate::r#gen::Lake::Build::Job::Basic::l_Lake_instInhabitedJobState_default;
use crate::r#gen::Lake::Config::OutFormat::l_Lake_formatQuery___boxed;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::ffi::lean_task_pure;
use crate::ffi::{
    lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_lt, lean_nat_mul,
};
static mut l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_instInhabitedFacetConfig_default___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedFacetConfig_default___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedFacetConfig_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedFacetConfig_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedFacetConfig_default___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instInhabitedFacetConfig_default___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instInhabitedFacetConfig_default___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedFacetConfig_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instInhabitedFacetConfig_default___closed__2_value: crate::leanh::LeanCtorObject<
    5,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4
            + 8) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedFacetConfig_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instInhabitedFacetConfig_default___closed__1_value)
            as *mut crate::leanh::LeanObject,
        257 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instInhabitedFacetConfig_default___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedFacetConfig_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__3_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__3_value)
            as *mut crate::leanh::LeanObject,
        8504843326314613972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__5_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
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
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0,
    ],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__6_value)
            as *mut crate::leanh::LeanObject,
        17228437386856258271 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__9_value:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__10_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 97, 99, 116, 105, 99, 82, 102, 108, 0],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value:
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
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__10_value)
            as *mut crate::leanh::LeanObject,
        3294379458557754569 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_KFacetConfig_kind__eq___autoParam___closed__12_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [114, 102, 108, 0],
};
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_KFacetConfig_kind__eq___autoParam___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_KFacetConfig_kind__eq___autoParam: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 97, 107, 101, 0],
};
static mut l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        77, 111, 100, 117, 108, 101, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value:
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
        core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10746694949860878979 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameModuleFacetDecl_unsafe__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameModuleFacetDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        80, 97, 99, 107, 97, 103, 101, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15028798877229211815 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNamePackageFacetDecl_unsafe__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNamePackageFacetDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        76, 105, 98, 114, 97, 114, 121, 70, 97, 99, 101, 116, 68, 101, 99, 108, 0,
    ],
};
static mut l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13012506173997729135 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12077031116990493093 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameLibraryFacetDecl_unsafe__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instTypeNameLibraryFacetDecl: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = l_Lake_instInhabitedJobState_default;
    v___x_596_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_597_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_597_, 0, v___x_596_);
    crate::leanh::lean_ctor_set(v___x_597_, 1, v___x_595_);
    return v___x_597_;
}
pub unsafe fn _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0_once),
        _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0,
    );
    v___x_599_ = lean_task_pure(v___x_598_);
    return v___x_599_;
}
pub unsafe fn _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_601_: u8 = 0;
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = 0;
    v___x_602_ = l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2;
    v___x_603_ = crate::leanh::lean_box(0);
    v___x_604_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1_once),
        _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1,
    );
    v___x_605_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_605_, 0, v___x_604_);
    crate::leanh::lean_ctor_set(v___x_605_, 1, v___x_603_);
    crate::leanh::lean_ctor_set(v___x_605_, 2, v___x_602_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_605_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_601_,
    );
    return v___x_605_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig_default___lam__0(
    mut v_x_606_: *mut crate::leanh::LeanObject,
    mut v___y_607_: *mut crate::leanh::LeanObject,
    mut v___y_608_: *mut crate::leanh::LeanObject,
    mut v___y_609_: *mut crate::leanh::LeanObject,
    mut v___y_610_: *mut crate::leanh::LeanObject,
    mut v___y_611_: *mut crate::leanh::LeanObject,
    mut v___y_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_614_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3_once),
        _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3,
    );
    v___x_615_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_615_, 0, v___x_614_);
    crate::leanh::lean_ctor_set(v___x_615_, 1, v___y_612_);
    return v___x_615_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig_default___lam__0___boxed(
    mut v_x_616_: *mut crate::leanh::LeanObject,
    mut v___y_617_: *mut crate::leanh::LeanObject,
    mut v___y_618_: *mut crate::leanh::LeanObject,
    mut v___y_619_: *mut crate::leanh::LeanObject,
    mut v___y_620_: *mut crate::leanh::LeanObject,
    mut v___y_621_: *mut crate::leanh::LeanObject,
    mut v___y_622_: *mut crate::leanh::LeanObject,
    mut v___y_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_624_ = l_Lake_instInhabitedFacetConfig_default___lam__0(
        v_x_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_,
    );
    crate::leanh::lean_dec_ref(v___y_621_);
    crate::leanh::lean_dec(v___y_620_);
    crate::leanh::lean_dec(v___y_619_);
    crate::leanh::lean_dec(v___y_618_);
    crate::leanh::lean_dec_ref(v___y_617_);
    crate::leanh::lean_dec(v_x_616_);
    return v_res_624_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig_default___lam__1(
    mut v_x_625_: u8,
    mut v___y_626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_627_ = l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2;
    return v___x_627_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig_default___lam__1___boxed(
    mut v_x_628_: *mut crate::leanh::LeanObject,
    mut v___y_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_437__boxed_630_: u8 = 0;
    let mut v_res_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_437__boxed_630_ = (crate::leanh::lean_unbox(v_x_628_) as u8);
    v_res_631_ = l_Lake_instInhabitedFacetConfig_default___lam__1(v_x_437__boxed_630_, v___y_629_);
    crate::leanh::lean_dec(v___y_629_);
    return v_res_631_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig_default(
    mut v_name_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lake_instInhabitedFacetConfig_default___closed__2;
    return v___x_640_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig_default___boxed(
    mut v_name_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l_Lake_instInhabitedFacetConfig_default(v_name_641_);
    crate::leanh::lean_dec(v_name_641_);
    return v_res_642_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig(
    mut v_a_643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_644_ = l_Lake_instInhabitedFacetConfig_default(v_a_643_);
    return v___x_644_;
}
pub unsafe fn l_Lake_instInhabitedFacetConfig___boxed(
    mut v_a_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_646_ = l_Lake_instInhabitedFacetConfig(v_a_645_);
    crate::leanh::lean_dec(v_a_645_);
    return v_res_646_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0___redArg(
    mut v_t_647_: *mut crate::leanh::LeanObject,
    mut v_k_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_647_) == 0 {
                    v_k_649_ = crate::leanh::lean_ctor_get(v_t_647_, 1);
                    v_v_650_ = crate::leanh::lean_ctor_get(v_t_647_, 2);
                    v_l_651_ = crate::leanh::lean_ctor_get(v_t_647_, 3);
                    v_r_652_ = crate::leanh::lean_ctor_get(v_t_647_, 4);
                    v___x_653_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_648_, v_k_649_);
                    match v___x_653_ {
                        0 => {
                            v_t_647_ = v_l_651_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_650_);
                            v___x_655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_655_, 0, v_v_650_);
                            return v___x_655_;
                        }
                        _ => {
                            v_t_647_ = v_r_652_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_657_ = crate::leanh::lean_box(0);
                    return v___x_657_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0___redArg___boxed(
    mut v_t_658_: *mut crate::leanh::LeanObject,
    mut v_k_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0___redArg(
            v_t_658_, v_k_659_,
        );
    crate::leanh::lean_dec(v_k_659_);
    crate::leanh::lean_dec(v_t_658_);
    return v_res_660_;
}
pub unsafe fn l_Lake_FacetConfigMap_get_x3f(
    mut v_name_661_: *mut crate::leanh::LeanObject,
    mut v_self_662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_663_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0___redArg(
            v_self_662_,
            v_name_661_,
        );
    return v___x_663_;
}
pub unsafe fn l_Lake_FacetConfigMap_get_x3f___boxed(
    mut v_name_664_: *mut crate::leanh::LeanObject,
    mut v_self_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Lake_FacetConfigMap_get_x3f(v_name_664_, v_self_665_);
    crate::leanh::lean_dec(v_self_665_);
    crate::leanh::lean_dec(v_name_664_);
    return v_res_666_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0(
    mut v_00_u03b2_667_: *mut crate::leanh::LeanObject,
    mut v_inst_668_: *mut crate::leanh::LeanObject,
    mut v_t_669_: *mut crate::leanh::LeanObject,
    mut v_k_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ =
        l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0___redArg(
            v_t_669_, v_k_670_,
        );
    return v___x_671_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0___boxed(
    mut v_00_u03b2_672_: *mut crate::leanh::LeanObject,
    mut v_inst_673_: *mut crate::leanh::LeanObject,
    mut v_t_674_: *mut crate::leanh::LeanObject,
    mut v_k_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_676_ = l_Std_DTreeMap_Internal_Impl_get_x3f___at___00Lake_FacetConfigMap_get_x3f_spec__0(
        v_00_u03b2_672_,
        v_inst_673_,
        v_t_674_,
        v_k_675_,
    );
    crate::leanh::lean_dec(v_k_675_);
    crate::leanh::lean_dec(v_t_674_);
    return v_res_676_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_FacetConfigMap_insert_spec__0___redArg(
    mut v_k_677_: *mut crate::leanh::LeanObject,
    mut v_v_678_: *mut crate::leanh::LeanObject,
    mut v_t_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_687_: u8 = 0;
    let mut v___x_688_: u8 = 0;
    let mut v_impl_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: u8 = 0;
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_707_: u8 = 0;
    let mut v_size_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: u8 = 0;
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_719_: u8 = 0;
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_745_: u8 = 0;
    let mut v_unused_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_759_: u8 = 0;
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_763_: u8 = 0;
    let mut v_unused_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut v_unused_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_782_: u8 = 0;
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut v_unused_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_798_: u8 = 0;
    let mut v_k_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_803_: u8 = 0;
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut v_unused_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_818_: u8 = 0;
    let mut v_unused_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: u8 = 0;
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v_size_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: u8 = 0;
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_unused_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_unused_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_unused_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_920_: u8 = 0;
    let mut v_k_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_936_: u8 = 0;
    let mut v_unused_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut v_unused_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_956_: u8 = 0;
    let mut v_unused_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_679_) == 0 {
                    v_size_680_ = crate::leanh::lean_ctor_get(v_t_679_, 0);
                    v_k_681_ = crate::leanh::lean_ctor_get(v_t_679_, 1);
                    v_v_682_ = crate::leanh::lean_ctor_get(v_t_679_, 2);
                    v_l_683_ = crate::leanh::lean_ctor_get(v_t_679_, 3);
                    v_r_684_ = crate::leanh::lean_ctor_get(v_t_679_, 4);
                    v_isSharedCheck_964_ = (!crate::leanh::lean_is_exclusive(v_t_679_)) as u8;
                    if v_isSharedCheck_964_ == 0 {
                        v___x_686_ = v_t_679_;
                        v_isShared_687_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_684_);
                        crate::leanh::lean_inc(v_l_683_);
                        crate::leanh::lean_inc(v_v_682_);
                        crate::leanh::lean_inc(v_k_681_);
                        crate::leanh::lean_inc(v_size_680_);
                        crate::leanh::lean_dec(v_t_679_);
                        v___x_686_ = crate::leanh::lean_box(0);
                        v_isShared_687_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_965_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_966_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_966_, 0, v___x_965_);
                    crate::leanh::lean_ctor_set(v___x_966_, 1, v_k_677_);
                    crate::leanh::lean_ctor_set(v___x_966_, 2, v_v_678_);
                    crate::leanh::lean_ctor_set(v___x_966_, 3, v_t_679_);
                    crate::leanh::lean_ctor_set(v___x_966_, 4, v_t_679_);
                    return v___x_966_;
                }
            }
            1 => {
                v___x_688_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_677_, v_k_681_);
                match v___x_688_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_680_);
                        v_impl_689_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_FacetConfigMap_insert_spec__0___redArg(v_k_677_, v_v_678_, v_l_683_);
                        v___x_690_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_684_) == 0 {
                            v_size_691_ = crate::leanh::lean_ctor_get(v_r_684_, 0);
                            v_size_692_ = crate::leanh::lean_ctor_get(v_impl_689_, 0);
                            crate::leanh::lean_inc(v_size_692_);
                            v_k_693_ = crate::leanh::lean_ctor_get(v_impl_689_, 1);
                            crate::leanh::lean_inc(v_k_693_);
                            v_v_694_ = crate::leanh::lean_ctor_get(v_impl_689_, 2);
                            crate::leanh::lean_inc(v_v_694_);
                            v_l_695_ = crate::leanh::lean_ctor_get(v_impl_689_, 3);
                            crate::leanh::lean_inc(v_l_695_);
                            v_r_696_ = crate::leanh::lean_ctor_get(v_impl_689_, 4);
                            crate::leanh::lean_inc(v_r_696_);
                            v___x_697_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_698_ = lean_nat_mul(v___x_697_, v_size_691_);
                            v___x_699_ = lean_nat_dec_lt(v___x_698_, v_size_692_);
                            crate::leanh::lean_dec(v___x_698_);
                            if v___x_699_ == 0 {
                                crate::leanh::lean_dec(v_r_696_);
                                crate::leanh::lean_dec(v_l_695_);
                                crate::leanh::lean_dec(v_v_694_);
                                crate::leanh::lean_dec(v_k_693_);
                                v___x_700_ = lean_nat_add(v___x_690_, v_size_692_);
                                crate::leanh::lean_dec(v_size_692_);
                                v___x_701_ = lean_nat_add(v___x_700_, v_size_691_);
                                crate::leanh::lean_dec(v___x_700_);
                                if v_isShared_687_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_686_, 3, v_impl_689_);
                                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_701_);
                                    v___x_703_ = v___x_686_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_704_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_704_,
                                        0,
                                        v___x_701_,
                                    );
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_704_, 1, v_k_681_);
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_704_, 2, v_v_682_);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_704_,
                                        3,
                                        v_impl_689_,
                                    );
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_704_, 4, v_r_684_);
                                    v___x_703_ = v_reuseFailAlloc_704_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_770_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_689_)) as u8;
                                if v_isSharedCheck_770_ == 0 {
                                    v_unused_771_ = crate::leanh::lean_ctor_get(v_impl_689_, 4);
                                    crate::leanh::lean_dec(v_unused_771_);
                                    v_unused_772_ = crate::leanh::lean_ctor_get(v_impl_689_, 3);
                                    crate::leanh::lean_dec(v_unused_772_);
                                    v_unused_773_ = crate::leanh::lean_ctor_get(v_impl_689_, 2);
                                    crate::leanh::lean_dec(v_unused_773_);
                                    v_unused_774_ = crate::leanh::lean_ctor_get(v_impl_689_, 1);
                                    crate::leanh::lean_dec(v_unused_774_);
                                    v_unused_775_ = crate::leanh::lean_ctor_get(v_impl_689_, 0);
                                    crate::leanh::lean_dec(v_unused_775_);
                                    v___x_706_ = v_impl_689_;
                                    v_isShared_707_ = v_isSharedCheck_770_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_689_);
                                    v___x_706_ = crate::leanh::lean_box(0);
                                    v_isShared_707_ = v_isSharedCheck_770_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_776_ = crate::leanh::lean_ctor_get(v_impl_689_, 3);
                            crate::leanh::lean_inc(v_l_776_);
                            if crate::leanh::lean_obj_tag(v_l_776_) == 0 {
                                v_r_777_ = crate::leanh::lean_ctor_get(v_impl_689_, 4);
                                v_k_778_ = crate::leanh::lean_ctor_get(v_impl_689_, 1);
                                v_v_779_ = crate::leanh::lean_ctor_get(v_impl_689_, 2);
                                v_isSharedCheck_790_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_689_)) as u8;
                                if v_isSharedCheck_790_ == 0 {
                                    v_unused_791_ = crate::leanh::lean_ctor_get(v_impl_689_, 3);
                                    crate::leanh::lean_dec(v_unused_791_);
                                    v_unused_792_ = crate::leanh::lean_ctor_get(v_impl_689_, 0);
                                    crate::leanh::lean_dec(v_unused_792_);
                                    v___x_781_ = v_impl_689_;
                                    v_isShared_782_ = v_isSharedCheck_790_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_777_);
                                    crate::leanh::lean_inc(v_v_779_);
                                    crate::leanh::lean_inc(v_k_778_);
                                    crate::leanh::lean_dec(v_impl_689_);
                                    v___x_781_ = crate::leanh::lean_box(0);
                                    v_isShared_782_ = v_isSharedCheck_790_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_793_ = crate::leanh::lean_ctor_get(v_impl_689_, 4);
                                crate::leanh::lean_inc(v_r_793_);
                                if crate::leanh::lean_obj_tag(v_r_793_) == 0 {
                                    v_k_794_ = crate::leanh::lean_ctor_get(v_impl_689_, 1);
                                    v_v_795_ = crate::leanh::lean_ctor_get(v_impl_689_, 2);
                                    v_isSharedCheck_818_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_689_)) as u8;
                                    if v_isSharedCheck_818_ == 0 {
                                        v_unused_819_ = crate::leanh::lean_ctor_get(v_impl_689_, 4);
                                        crate::leanh::lean_dec(v_unused_819_);
                                        v_unused_820_ = crate::leanh::lean_ctor_get(v_impl_689_, 3);
                                        crate::leanh::lean_dec(v_unused_820_);
                                        v_unused_821_ = crate::leanh::lean_ctor_get(v_impl_689_, 0);
                                        crate::leanh::lean_dec(v_unused_821_);
                                        v___x_797_ = v_impl_689_;
                                        v_isShared_798_ = v_isSharedCheck_818_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_795_);
                                        crate::leanh::lean_inc(v_k_794_);
                                        crate::leanh::lean_dec(v_impl_689_);
                                        v___x_797_ = crate::leanh::lean_box(0);
                                        v_isShared_798_ = v_isSharedCheck_818_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_822_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_687_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_686_, 4, v_r_793_);
                                        crate::leanh::lean_ctor_set(v___x_686_, 3, v_impl_689_);
                                        crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_822_);
                                        v___x_824_ = v___x_686_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_825_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_825_,
                                            0,
                                            v___x_822_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_825_,
                                            1,
                                            v_k_681_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_825_,
                                            2,
                                            v_v_682_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_825_,
                                            3,
                                            v_impl_689_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_825_,
                                            4,
                                            v_r_793_,
                                        );
                                        v___x_824_ = v_reuseFailAlloc_825_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_682_);
                        crate::leanh::lean_dec(v_k_681_);
                        if v_isShared_687_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_686_, 2, v_v_678_);
                            crate::leanh::lean_ctor_set(v___x_686_, 1, v_k_677_);
                            v___x_827_ = v___x_686_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_828_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 0, v_size_680_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_677_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_678_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 3, v_l_683_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_828_, 4, v_r_684_);
                            v___x_827_ = v_reuseFailAlloc_828_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_680_);
                        v_impl_829_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_FacetConfigMap_insert_spec__0___redArg(v_k_677_, v_v_678_, v_r_684_);
                        v___x_830_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_683_) == 0 {
                            v_size_831_ = crate::leanh::lean_ctor_get(v_l_683_, 0);
                            v_size_832_ = crate::leanh::lean_ctor_get(v_impl_829_, 0);
                            crate::leanh::lean_inc(v_size_832_);
                            v_k_833_ = crate::leanh::lean_ctor_get(v_impl_829_, 1);
                            crate::leanh::lean_inc(v_k_833_);
                            v_v_834_ = crate::leanh::lean_ctor_get(v_impl_829_, 2);
                            crate::leanh::lean_inc(v_v_834_);
                            v_l_835_ = crate::leanh::lean_ctor_get(v_impl_829_, 3);
                            crate::leanh::lean_inc(v_l_835_);
                            v_r_836_ = crate::leanh::lean_ctor_get(v_impl_829_, 4);
                            crate::leanh::lean_inc(v_r_836_);
                            v___x_837_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_838_ = lean_nat_mul(v___x_837_, v_size_831_);
                            v___x_839_ = lean_nat_dec_lt(v___x_838_, v_size_832_);
                            crate::leanh::lean_dec(v___x_838_);
                            if v___x_839_ == 0 {
                                crate::leanh::lean_dec(v_r_836_);
                                crate::leanh::lean_dec(v_l_835_);
                                crate::leanh::lean_dec(v_v_834_);
                                crate::leanh::lean_dec(v_k_833_);
                                v___x_840_ = lean_nat_add(v___x_830_, v_size_831_);
                                v___x_841_ = lean_nat_add(v___x_840_, v_size_832_);
                                crate::leanh::lean_dec(v_size_832_);
                                crate::leanh::lean_dec(v___x_840_);
                                if v_isShared_687_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_686_, 4, v_impl_829_);
                                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_841_);
                                    v___x_843_ = v___x_686_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_844_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_844_,
                                        0,
                                        v___x_841_,
                                    );
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_844_, 1, v_k_681_);
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_844_, 2, v_v_682_);
                                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_844_, 3, v_l_683_);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_844_,
                                        4,
                                        v_impl_829_,
                                    );
                                    v___x_843_ = v_reuseFailAlloc_844_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_908_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_829_)) as u8;
                                if v_isSharedCheck_908_ == 0 {
                                    v_unused_909_ = crate::leanh::lean_ctor_get(v_impl_829_, 4);
                                    crate::leanh::lean_dec(v_unused_909_);
                                    v_unused_910_ = crate::leanh::lean_ctor_get(v_impl_829_, 3);
                                    crate::leanh::lean_dec(v_unused_910_);
                                    v_unused_911_ = crate::leanh::lean_ctor_get(v_impl_829_, 2);
                                    crate::leanh::lean_dec(v_unused_911_);
                                    v_unused_912_ = crate::leanh::lean_ctor_get(v_impl_829_, 1);
                                    crate::leanh::lean_dec(v_unused_912_);
                                    v_unused_913_ = crate::leanh::lean_ctor_get(v_impl_829_, 0);
                                    crate::leanh::lean_dec(v_unused_913_);
                                    v___x_846_ = v_impl_829_;
                                    v_isShared_847_ = v_isSharedCheck_908_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_829_);
                                    v___x_846_ = crate::leanh::lean_box(0);
                                    v_isShared_847_ = v_isSharedCheck_908_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_914_ = crate::leanh::lean_ctor_get(v_impl_829_, 3);
                            crate::leanh::lean_inc(v_l_914_);
                            if crate::leanh::lean_obj_tag(v_l_914_) == 0 {
                                v_r_915_ = crate::leanh::lean_ctor_get(v_impl_829_, 4);
                                v_k_916_ = crate::leanh::lean_ctor_get(v_impl_829_, 1);
                                v_v_917_ = crate::leanh::lean_ctor_get(v_impl_829_, 2);
                                v_isSharedCheck_940_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_829_)) as u8;
                                if v_isSharedCheck_940_ == 0 {
                                    v_unused_941_ = crate::leanh::lean_ctor_get(v_impl_829_, 3);
                                    crate::leanh::lean_dec(v_unused_941_);
                                    v_unused_942_ = crate::leanh::lean_ctor_get(v_impl_829_, 0);
                                    crate::leanh::lean_dec(v_unused_942_);
                                    v___x_919_ = v_impl_829_;
                                    v_isShared_920_ = v_isSharedCheck_940_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_915_);
                                    crate::leanh::lean_inc(v_v_917_);
                                    crate::leanh::lean_inc(v_k_916_);
                                    crate::leanh::lean_dec(v_impl_829_);
                                    v___x_919_ = crate::leanh::lean_box(0);
                                    v_isShared_920_ = v_isSharedCheck_940_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_943_ = crate::leanh::lean_ctor_get(v_impl_829_, 4);
                                crate::leanh::lean_inc(v_r_943_);
                                if crate::leanh::lean_obj_tag(v_r_943_) == 0 {
                                    v_k_944_ = crate::leanh::lean_ctor_get(v_impl_829_, 1);
                                    v_v_945_ = crate::leanh::lean_ctor_get(v_impl_829_, 2);
                                    v_isSharedCheck_956_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_829_)) as u8;
                                    if v_isSharedCheck_956_ == 0 {
                                        v_unused_957_ = crate::leanh::lean_ctor_get(v_impl_829_, 4);
                                        crate::leanh::lean_dec(v_unused_957_);
                                        v_unused_958_ = crate::leanh::lean_ctor_get(v_impl_829_, 3);
                                        crate::leanh::lean_dec(v_unused_958_);
                                        v_unused_959_ = crate::leanh::lean_ctor_get(v_impl_829_, 0);
                                        crate::leanh::lean_dec(v_unused_959_);
                                        v___x_947_ = v_impl_829_;
                                        v_isShared_948_ = v_isSharedCheck_956_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_945_);
                                        crate::leanh::lean_inc(v_k_944_);
                                        crate::leanh::lean_dec(v_impl_829_);
                                        v___x_947_ = crate::leanh::lean_box(0);
                                        v_isShared_948_ = v_isSharedCheck_956_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_960_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_687_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_686_, 4, v_impl_829_);
                                        crate::leanh::lean_ctor_set(v___x_686_, 3, v_r_943_);
                                        crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_960_);
                                        v___x_962_ = v___x_686_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_963_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_963_,
                                            0,
                                            v___x_960_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_963_,
                                            1,
                                            v_k_681_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_963_,
                                            2,
                                            v_v_682_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_963_,
                                            3,
                                            v_r_943_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_963_,
                                            4,
                                            v_impl_829_,
                                        );
                                        v___x_962_ = v_reuseFailAlloc_963_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_703_;
            }
            3 => {
                v_size_708_ = crate::leanh::lean_ctor_get(v_l_695_, 0);
                v_size_709_ = crate::leanh::lean_ctor_get(v_r_696_, 0);
                v_k_710_ = crate::leanh::lean_ctor_get(v_r_696_, 1);
                v_v_711_ = crate::leanh::lean_ctor_get(v_r_696_, 2);
                v_l_712_ = crate::leanh::lean_ctor_get(v_r_696_, 3);
                v_r_713_ = crate::leanh::lean_ctor_get(v_r_696_, 4);
                v___x_714_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_715_ = lean_nat_mul(v___x_714_, v_size_708_);
                v___x_716_ = lean_nat_dec_lt(v_size_709_, v___x_715_);
                crate::leanh::lean_dec(v___x_715_);
                if v___x_716_ == 0 {
                    crate::leanh::lean_inc(v_r_713_);
                    crate::leanh::lean_inc(v_l_712_);
                    crate::leanh::lean_inc(v_v_711_);
                    crate::leanh::lean_inc(v_k_710_);
                    v_isSharedCheck_745_ = (!crate::leanh::lean_is_exclusive(v_r_696_)) as u8;
                    if v_isSharedCheck_745_ == 0 {
                        v_unused_746_ = crate::leanh::lean_ctor_get(v_r_696_, 4);
                        crate::leanh::lean_dec(v_unused_746_);
                        v_unused_747_ = crate::leanh::lean_ctor_get(v_r_696_, 3);
                        crate::leanh::lean_dec(v_unused_747_);
                        v_unused_748_ = crate::leanh::lean_ctor_get(v_r_696_, 2);
                        crate::leanh::lean_dec(v_unused_748_);
                        v_unused_749_ = crate::leanh::lean_ctor_get(v_r_696_, 1);
                        crate::leanh::lean_dec(v_unused_749_);
                        v_unused_750_ = crate::leanh::lean_ctor_get(v_r_696_, 0);
                        crate::leanh::lean_dec(v_unused_750_);
                        v___x_718_ = v_r_696_;
                        v_isShared_719_ = v_isSharedCheck_745_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_696_);
                        v___x_718_ = crate::leanh::lean_box(0);
                        v_isShared_719_ = v_isSharedCheck_745_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_686_);
                    v___x_751_ = lean_nat_add(v___x_690_, v_size_692_);
                    crate::leanh::lean_dec(v_size_692_);
                    v___x_752_ = lean_nat_add(v___x_751_, v_size_691_);
                    crate::leanh::lean_dec(v___x_751_);
                    v___x_753_ = lean_nat_add(v___x_690_, v_size_691_);
                    v___x_754_ = lean_nat_add(v___x_753_, v_size_709_);
                    crate::leanh::lean_dec(v___x_753_);
                    crate::leanh::lean_inc_ref(v_r_684_);
                    if v_isShared_707_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_706_, 4, v_r_684_);
                        crate::leanh::lean_ctor_set(v___x_706_, 3, v_r_696_);
                        crate::leanh::lean_ctor_set(v___x_706_, 2, v_v_682_);
                        crate::leanh::lean_ctor_set(v___x_706_, 1, v_k_681_);
                        crate::leanh::lean_ctor_set(v___x_706_, 0, v___x_754_);
                        v___x_756_ = v___x_706_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_769_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_754_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 1, v_k_681_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 2, v_v_682_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 3, v_r_696_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_769_, 4, v_r_684_);
                        v___x_756_ = v_reuseFailAlloc_769_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_720_ = lean_nat_add(v___x_690_, v_size_692_);
                crate::leanh::lean_dec(v_size_692_);
                v___x_721_ = lean_nat_add(v___x_720_, v_size_691_);
                crate::leanh::lean_dec(v___x_720_);
                v___x_733_ = lean_nat_add(v___x_690_, v_size_708_);
                if crate::leanh::lean_obj_tag(v_l_712_) == 0 {
                    v_size_743_ = crate::leanh::lean_ctor_get(v_l_712_, 0);
                    crate::leanh::lean_inc(v_size_743_);
                    v___y_735_ = v_size_743_;
                    state = 8;
                    continue;
                } else {
                    v___x_744_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_735_ = v___x_744_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_726_ = lean_nat_add(v___y_724_, v___y_725_);
                crate::leanh::lean_dec(v___y_725_);
                crate::leanh::lean_dec(v___y_724_);
                if v_isShared_719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_718_, 4, v_r_684_);
                    crate::leanh::lean_ctor_set(v___x_718_, 3, v_r_713_);
                    crate::leanh::lean_ctor_set(v___x_718_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v___x_718_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v___x_718_, 0, v___x_726_);
                    v___x_728_ = v___x_718_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_732_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_726_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 3, v_r_713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 4, v_r_684_);
                    v___x_728_ = v_reuseFailAlloc_732_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_707_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_706_, 4, v___x_728_);
                    crate::leanh::lean_ctor_set(v___x_706_, 3, v___y_723_);
                    crate::leanh::lean_ctor_set(v___x_706_, 2, v_v_711_);
                    crate::leanh::lean_ctor_set(v___x_706_, 1, v_k_710_);
                    crate::leanh::lean_ctor_set(v___x_706_, 0, v___x_721_);
                    v___x_730_ = v___x_706_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_731_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 1, v_k_710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 2, v_v_711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 3, v___y_723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_731_, 4, v___x_728_);
                    v___x_730_ = v_reuseFailAlloc_731_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_730_;
            }
            8 => {
                v___x_736_ = lean_nat_add(v___x_733_, v___y_735_);
                crate::leanh::lean_dec(v___y_735_);
                crate::leanh::lean_dec(v___x_733_);
                if v_isShared_687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_686_, 4, v_l_712_);
                    crate::leanh::lean_ctor_set(v___x_686_, 3, v_l_695_);
                    crate::leanh::lean_ctor_set(v___x_686_, 2, v_v_694_);
                    crate::leanh::lean_ctor_set(v___x_686_, 1, v_k_693_);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_736_);
                    v___x_738_ = v___x_686_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_742_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_736_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 1, v_k_693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 2, v_v_694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 3, v_l_695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 4, v_l_712_);
                    v___x_738_ = v_reuseFailAlloc_742_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_739_ = lean_nat_add(v___x_690_, v_size_691_);
                if crate::leanh::lean_obj_tag(v_r_713_) == 0 {
                    v_size_740_ = crate::leanh::lean_ctor_get(v_r_713_, 0);
                    crate::leanh::lean_inc(v_size_740_);
                    v___y_723_ = v___x_738_;
                    v___y_724_ = v___x_739_;
                    v___y_725_ = v_size_740_;
                    state = 5;
                    continue;
                } else {
                    v___x_741_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_723_ = v___x_738_;
                    v___y_724_ = v___x_739_;
                    v___y_725_ = v___x_741_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_763_ = (!crate::leanh::lean_is_exclusive(v_r_684_)) as u8;
                if v_isSharedCheck_763_ == 0 {
                    v_unused_764_ = crate::leanh::lean_ctor_get(v_r_684_, 4);
                    crate::leanh::lean_dec(v_unused_764_);
                    v_unused_765_ = crate::leanh::lean_ctor_get(v_r_684_, 3);
                    crate::leanh::lean_dec(v_unused_765_);
                    v_unused_766_ = crate::leanh::lean_ctor_get(v_r_684_, 2);
                    crate::leanh::lean_dec(v_unused_766_);
                    v_unused_767_ = crate::leanh::lean_ctor_get(v_r_684_, 1);
                    crate::leanh::lean_dec(v_unused_767_);
                    v_unused_768_ = crate::leanh::lean_ctor_get(v_r_684_, 0);
                    crate::leanh::lean_dec(v_unused_768_);
                    v___x_758_ = v_r_684_;
                    v_isShared_759_ = v_isSharedCheck_763_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_684_);
                    v___x_758_ = crate::leanh::lean_box(0);
                    v_isShared_759_ = v_isSharedCheck_763_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_758_, 4, v___x_756_);
                    crate::leanh::lean_ctor_set(v___x_758_, 3, v_l_695_);
                    crate::leanh::lean_ctor_set(v___x_758_, 2, v_v_694_);
                    crate::leanh::lean_ctor_set(v___x_758_, 1, v_k_693_);
                    crate::leanh::lean_ctor_set(v___x_758_, 0, v___x_752_);
                    v___x_761_ = v___x_758_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_762_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 1, v_k_693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 2, v_v_694_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 3, v_l_695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_762_, 4, v___x_756_);
                    v___x_761_ = v_reuseFailAlloc_762_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_761_;
            }
            13 => {
                v___x_783_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_777_);
                if v_isShared_782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_781_, 3, v_r_777_);
                    crate::leanh::lean_ctor_set(v___x_781_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v___x_781_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v___x_781_, 0, v___x_690_);
                    v___x_785_ = v___x_781_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 3, v_r_777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 4, v_r_777_);
                    v___x_785_ = v_reuseFailAlloc_789_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_686_, 4, v___x_785_);
                    crate::leanh::lean_ctor_set(v___x_686_, 3, v_l_776_);
                    crate::leanh::lean_ctor_set(v___x_686_, 2, v_v_779_);
                    crate::leanh::lean_ctor_set(v___x_686_, 1, v_k_778_);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_783_);
                    v___x_787_ = v___x_686_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_788_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 1, v_k_778_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 2, v_v_779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 3, v_l_776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 4, v___x_785_);
                    v___x_787_ = v_reuseFailAlloc_788_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_787_;
            }
            16 => {
                v_k_799_ = crate::leanh::lean_ctor_get(v_r_793_, 1);
                v_v_800_ = crate::leanh::lean_ctor_get(v_r_793_, 2);
                v_isSharedCheck_814_ = (!crate::leanh::lean_is_exclusive(v_r_793_)) as u8;
                if v_isSharedCheck_814_ == 0 {
                    v_unused_815_ = crate::leanh::lean_ctor_get(v_r_793_, 4);
                    crate::leanh::lean_dec(v_unused_815_);
                    v_unused_816_ = crate::leanh::lean_ctor_get(v_r_793_, 3);
                    crate::leanh::lean_dec(v_unused_816_);
                    v_unused_817_ = crate::leanh::lean_ctor_get(v_r_793_, 0);
                    crate::leanh::lean_dec(v_unused_817_);
                    v___x_802_ = v_r_793_;
                    v_isShared_803_ = v_isSharedCheck_814_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_800_);
                    crate::leanh::lean_inc(v_k_799_);
                    crate::leanh::lean_dec(v_r_793_);
                    v___x_802_ = crate::leanh::lean_box(0);
                    v_isShared_803_ = v_isSharedCheck_814_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_804_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_803_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_802_, 4, v_l_776_);
                    crate::leanh::lean_ctor_set(v___x_802_, 3, v_l_776_);
                    crate::leanh::lean_ctor_set(v___x_802_, 2, v_v_795_);
                    crate::leanh::lean_ctor_set(v___x_802_, 1, v_k_794_);
                    crate::leanh::lean_ctor_set(v___x_802_, 0, v___x_690_);
                    v___x_806_ = v___x_802_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 3, v_l_776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_813_, 4, v_l_776_);
                    v___x_806_ = v_reuseFailAlloc_813_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_798_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_797_, 4, v_l_776_);
                    crate::leanh::lean_ctor_set(v___x_797_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v___x_797_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v___x_797_, 0, v___x_690_);
                    v___x_808_ = v___x_797_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_812_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_690_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 3, v_l_776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_812_, 4, v_l_776_);
                    v___x_808_ = v_reuseFailAlloc_812_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_686_, 4, v___x_808_);
                    crate::leanh::lean_ctor_set(v___x_686_, 3, v___x_806_);
                    crate::leanh::lean_ctor_set(v___x_686_, 2, v_v_800_);
                    crate::leanh::lean_ctor_set(v___x_686_, 1, v_k_799_);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_804_);
                    v___x_810_ = v___x_686_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_811_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 1, v_k_799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 2, v_v_800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 3, v___x_806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_811_, 4, v___x_808_);
                    v___x_810_ = v_reuseFailAlloc_811_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_810_;
            }
            21 => {
                return v___x_824_;
            }
            22 => {
                return v___x_827_;
            }
            23 => {
                return v___x_843_;
            }
            24 => {
                v_size_848_ = crate::leanh::lean_ctor_get(v_l_835_, 0);
                v_k_849_ = crate::leanh::lean_ctor_get(v_l_835_, 1);
                v_v_850_ = crate::leanh::lean_ctor_get(v_l_835_, 2);
                v_l_851_ = crate::leanh::lean_ctor_get(v_l_835_, 3);
                v_r_852_ = crate::leanh::lean_ctor_get(v_l_835_, 4);
                v_size_853_ = crate::leanh::lean_ctor_get(v_r_836_, 0);
                v___x_854_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_855_ = lean_nat_mul(v___x_854_, v_size_853_);
                v___x_856_ = lean_nat_dec_lt(v_size_848_, v___x_855_);
                crate::leanh::lean_dec(v___x_855_);
                if v___x_856_ == 0 {
                    crate::leanh::lean_inc(v_r_852_);
                    crate::leanh::lean_inc(v_l_851_);
                    crate::leanh::lean_inc(v_v_850_);
                    crate::leanh::lean_inc(v_k_849_);
                    v_isSharedCheck_884_ = (!crate::leanh::lean_is_exclusive(v_l_835_)) as u8;
                    if v_isSharedCheck_884_ == 0 {
                        v_unused_885_ = crate::leanh::lean_ctor_get(v_l_835_, 4);
                        crate::leanh::lean_dec(v_unused_885_);
                        v_unused_886_ = crate::leanh::lean_ctor_get(v_l_835_, 3);
                        crate::leanh::lean_dec(v_unused_886_);
                        v_unused_887_ = crate::leanh::lean_ctor_get(v_l_835_, 2);
                        crate::leanh::lean_dec(v_unused_887_);
                        v_unused_888_ = crate::leanh::lean_ctor_get(v_l_835_, 1);
                        crate::leanh::lean_dec(v_unused_888_);
                        v_unused_889_ = crate::leanh::lean_ctor_get(v_l_835_, 0);
                        crate::leanh::lean_dec(v_unused_889_);
                        v___x_858_ = v_l_835_;
                        v_isShared_859_ = v_isSharedCheck_884_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_835_);
                        v___x_858_ = crate::leanh::lean_box(0);
                        v_isShared_859_ = v_isSharedCheck_884_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_686_);
                    v___x_890_ = lean_nat_add(v___x_830_, v_size_831_);
                    v___x_891_ = lean_nat_add(v___x_890_, v_size_832_);
                    crate::leanh::lean_dec(v_size_832_);
                    v___x_892_ = lean_nat_add(v___x_890_, v_size_848_);
                    crate::leanh::lean_dec(v___x_890_);
                    crate::leanh::lean_inc_ref(v_l_683_);
                    if v_isShared_847_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_846_, 4, v_l_835_);
                        crate::leanh::lean_ctor_set(v___x_846_, 3, v_l_683_);
                        crate::leanh::lean_ctor_set(v___x_846_, 2, v_v_682_);
                        crate::leanh::lean_ctor_set(v___x_846_, 1, v_k_681_);
                        crate::leanh::lean_ctor_set(v___x_846_, 0, v___x_892_);
                        v___x_894_ = v___x_846_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_907_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_892_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 1, v_k_681_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 2, v_v_682_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 3, v_l_683_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 4, v_l_835_);
                        v___x_894_ = v_reuseFailAlloc_907_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_860_ = lean_nat_add(v___x_830_, v_size_831_);
                v___x_861_ = lean_nat_add(v___x_860_, v_size_832_);
                crate::leanh::lean_dec(v_size_832_);
                if crate::leanh::lean_obj_tag(v_l_851_) == 0 {
                    v_size_882_ = crate::leanh::lean_ctor_get(v_l_851_, 0);
                    crate::leanh::lean_inc(v_size_882_);
                    v___y_874_ = v_size_882_;
                    state = 29;
                    continue;
                } else {
                    v___x_883_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_874_ = v___x_883_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_866_ = lean_nat_add(v___y_863_, v___y_865_);
                crate::leanh::lean_dec(v___y_865_);
                crate::leanh::lean_dec(v___y_863_);
                if v_isShared_859_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_858_, 4, v_r_836_);
                    crate::leanh::lean_ctor_set(v___x_858_, 3, v_r_852_);
                    crate::leanh::lean_ctor_set(v___x_858_, 2, v_v_834_);
                    crate::leanh::lean_ctor_set(v___x_858_, 1, v_k_833_);
                    crate::leanh::lean_ctor_set(v___x_858_, 0, v___x_866_);
                    v___x_868_ = v___x_858_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_872_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 1, v_k_833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 2, v_v_834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 3, v_r_852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 4, v_r_836_);
                    v___x_868_ = v_reuseFailAlloc_872_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_846_, 4, v___x_868_);
                    crate::leanh::lean_ctor_set(v___x_846_, 3, v___y_864_);
                    crate::leanh::lean_ctor_set(v___x_846_, 2, v_v_850_);
                    crate::leanh::lean_ctor_set(v___x_846_, 1, v_k_849_);
                    crate::leanh::lean_ctor_set(v___x_846_, 0, v___x_861_);
                    v___x_870_ = v___x_846_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 1, v_k_849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 2, v_v_850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 3, v___y_864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 4, v___x_868_);
                    v___x_870_ = v_reuseFailAlloc_871_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_870_;
            }
            29 => {
                v___x_875_ = lean_nat_add(v___x_860_, v___y_874_);
                crate::leanh::lean_dec(v___y_874_);
                crate::leanh::lean_dec(v___x_860_);
                if v_isShared_687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_686_, 4, v_l_851_);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_875_);
                    v___x_877_ = v___x_686_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 3, v_l_683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_881_, 4, v_l_851_);
                    v___x_877_ = v_reuseFailAlloc_881_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_878_ = lean_nat_add(v___x_830_, v_size_853_);
                if crate::leanh::lean_obj_tag(v_r_852_) == 0 {
                    v_size_879_ = crate::leanh::lean_ctor_get(v_r_852_, 0);
                    crate::leanh::lean_inc(v_size_879_);
                    v___y_863_ = v___x_878_;
                    v___y_864_ = v___x_877_;
                    v___y_865_ = v_size_879_;
                    state = 26;
                    continue;
                } else {
                    v___x_880_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_863_ = v___x_878_;
                    v___y_864_ = v___x_877_;
                    v___y_865_ = v___x_880_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_901_ = (!crate::leanh::lean_is_exclusive(v_l_683_)) as u8;
                if v_isSharedCheck_901_ == 0 {
                    v_unused_902_ = crate::leanh::lean_ctor_get(v_l_683_, 4);
                    crate::leanh::lean_dec(v_unused_902_);
                    v_unused_903_ = crate::leanh::lean_ctor_get(v_l_683_, 3);
                    crate::leanh::lean_dec(v_unused_903_);
                    v_unused_904_ = crate::leanh::lean_ctor_get(v_l_683_, 2);
                    crate::leanh::lean_dec(v_unused_904_);
                    v_unused_905_ = crate::leanh::lean_ctor_get(v_l_683_, 1);
                    crate::leanh::lean_dec(v_unused_905_);
                    v_unused_906_ = crate::leanh::lean_ctor_get(v_l_683_, 0);
                    crate::leanh::lean_dec(v_unused_906_);
                    v___x_896_ = v_l_683_;
                    v_isShared_897_ = v_isSharedCheck_901_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_683_);
                    v___x_896_ = crate::leanh::lean_box(0);
                    v_isShared_897_ = v_isSharedCheck_901_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_896_, 4, v_r_836_);
                    crate::leanh::lean_ctor_set(v___x_896_, 3, v___x_894_);
                    crate::leanh::lean_ctor_set(v___x_896_, 2, v_v_834_);
                    crate::leanh::lean_ctor_set(v___x_896_, 1, v_k_833_);
                    crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_891_);
                    v___x_899_ = v___x_896_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 1, v_k_833_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 2, v_v_834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 3, v___x_894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 4, v_r_836_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_899_;
            }
            34 => {
                v_k_921_ = crate::leanh::lean_ctor_get(v_l_914_, 1);
                v_v_922_ = crate::leanh::lean_ctor_get(v_l_914_, 2);
                v_isSharedCheck_936_ = (!crate::leanh::lean_is_exclusive(v_l_914_)) as u8;
                if v_isSharedCheck_936_ == 0 {
                    v_unused_937_ = crate::leanh::lean_ctor_get(v_l_914_, 4);
                    crate::leanh::lean_dec(v_unused_937_);
                    v_unused_938_ = crate::leanh::lean_ctor_get(v_l_914_, 3);
                    crate::leanh::lean_dec(v_unused_938_);
                    v_unused_939_ = crate::leanh::lean_ctor_get(v_l_914_, 0);
                    crate::leanh::lean_dec(v_unused_939_);
                    v___x_924_ = v_l_914_;
                    v_isShared_925_ = v_isSharedCheck_936_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_922_);
                    crate::leanh::lean_inc(v_k_921_);
                    crate::leanh::lean_dec(v_l_914_);
                    v___x_924_ = crate::leanh::lean_box(0);
                    v_isShared_925_ = v_isSharedCheck_936_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_926_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_915_, 2);
                if v_isShared_925_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_924_, 4, v_r_915_);
                    crate::leanh::lean_ctor_set(v___x_924_, 3, v_r_915_);
                    crate::leanh::lean_ctor_set(v___x_924_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v___x_924_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v___x_924_, 0, v___x_830_);
                    v___x_928_ = v___x_924_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_935_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_935_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_935_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_935_, 3, v_r_915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_935_, 4, v_r_915_);
                    v___x_928_ = v_reuseFailAlloc_935_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_915_);
                if v_isShared_920_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_919_, 3, v_r_915_);
                    crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_830_);
                    v___x_930_ = v___x_919_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_934_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 1, v_k_916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 2, v_v_917_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 3, v_r_915_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_934_, 4, v_r_915_);
                    v___x_930_ = v_reuseFailAlloc_934_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_686_, 4, v___x_930_);
                    crate::leanh::lean_ctor_set(v___x_686_, 3, v___x_928_);
                    crate::leanh::lean_ctor_set(v___x_686_, 2, v_v_922_);
                    crate::leanh::lean_ctor_set(v___x_686_, 1, v_k_921_);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_926_);
                    v___x_932_ = v___x_686_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_933_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_926_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 1, v_k_921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 2, v_v_922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 3, v___x_928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 4, v___x_930_);
                    v___x_932_ = v_reuseFailAlloc_933_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_932_;
            }
            39 => {
                v___x_949_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_947_, 4, v_l_914_);
                    crate::leanh::lean_ctor_set(v___x_947_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v___x_947_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v___x_947_, 0, v___x_830_);
                    v___x_951_ = v___x_947_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_955_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_830_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 1, v_k_681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 2, v_v_682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 3, v_l_914_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_955_, 4, v_l_914_);
                    v___x_951_ = v_reuseFailAlloc_955_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_687_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_686_, 4, v_r_943_);
                    crate::leanh::lean_ctor_set(v___x_686_, 3, v___x_951_);
                    crate::leanh::lean_ctor_set(v___x_686_, 2, v_v_945_);
                    crate::leanh::lean_ctor_set(v___x_686_, 1, v_k_944_);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_949_);
                    v___x_953_ = v___x_686_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_954_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_954_, 1, v_k_944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_954_, 2, v_v_945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_954_, 3, v___x_951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_954_, 4, v_r_943_);
                    v___x_953_ = v_reuseFailAlloc_954_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_953_;
            }
            42 => {
                return v___x_962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_FacetConfigMap_insert(
    mut v_name_967_: *mut crate::leanh::LeanObject,
    mut v_cfg_968_: *mut crate::leanh::LeanObject,
    mut v_self_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_FacetConfigMap_insert_spec__0___redArg(
            v_name_967_,
            v_cfg_968_,
            v_self_969_,
        );
    return v___x_970_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_FacetConfigMap_insert_spec__0(
    mut v_00_u03b2_971_: *mut crate::leanh::LeanObject,
    mut v_k_972_: *mut crate::leanh::LeanObject,
    mut v_v_973_: *mut crate::leanh::LeanObject,
    mut v_t_974_: *mut crate::leanh::LeanObject,
    mut v_hl_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lake_FacetConfigMap_insert_spec__0___redArg(
            v_k_972_, v_v_973_, v_t_974_,
        );
    return v___x_976_;
}
pub unsafe fn l_Lake_FacetConfig_name___redArg(
    mut v_name_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_name_977_);
    return v_name_977_;
}
pub unsafe fn l_Lake_FacetConfig_name___redArg___boxed(
    mut v_name_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_979_ = l_Lake_FacetConfig_name___redArg(v_name_978_);
    crate::leanh::lean_dec(v_name_978_);
    return v_res_979_;
}
pub unsafe fn l_Lake_FacetConfig_name(
    mut v_name_980_: *mut crate::leanh::LeanObject,
    mut v_x_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_name_980_);
    return v_name_980_;
}
pub unsafe fn l_Lake_FacetConfig_name___boxed(
    mut v_name_982_: *mut crate::leanh::LeanObject,
    mut v_x_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Lake_FacetConfig_name(v_name_982_, v_x_983_);
    crate::leanh::lean_dec_ref(v_x_983_);
    crate::leanh::lean_dec(v_name_982_);
    return v_res_984_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__12;
    v___x_1013_ = l_Lean_mkAtom(v___x_1012_);
    return v___x_1013_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__13),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__13_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__13,
    );
    v___x_1015_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__5;
    v___x_1016_ = lean_array_push(v___x_1015_, v___x_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__14),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__14_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__14,
    );
    v___x_1018_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__11;
    v___x_1019_ = crate::leanh::lean_box(2);
    v___x_1020_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1020_, 0, v___x_1019_);
    crate::leanh::lean_ctor_set(v___x_1020_, 1, v___x_1018_);
    crate::leanh::lean_ctor_set(v___x_1020_, 2, v___x_1017_);
    return v___x_1020_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__15),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__15_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__15,
    );
    v___x_1022_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__5;
    v___x_1023_ = lean_array_push(v___x_1022_, v___x_1021_);
    return v___x_1023_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1024_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__16),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__16_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__16,
    );
    v___x_1025_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__9;
    v___x_1026_ = crate::leanh::lean_box(2);
    v___x_1027_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1027_, 0, v___x_1026_);
    crate::leanh::lean_ctor_set(v___x_1027_, 1, v___x_1025_);
    crate::leanh::lean_ctor_set(v___x_1027_, 2, v___x_1024_);
    return v___x_1027_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__17),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__17_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__17,
    );
    v___x_1029_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__5;
    v___x_1030_ = lean_array_push(v___x_1029_, v___x_1028_);
    return v___x_1030_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1031_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__18),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__18_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__18,
    );
    v___x_1032_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__7;
    v___x_1033_ = crate::leanh::lean_box(2);
    v___x_1034_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1034_, 0, v___x_1033_);
    crate::leanh::lean_ctor_set(v___x_1034_, 1, v___x_1032_);
    crate::leanh::lean_ctor_set(v___x_1034_, 2, v___x_1031_);
    return v___x_1034_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__19),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__19_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__19,
    );
    v___x_1036_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__5;
    v___x_1037_ = lean_array_push(v___x_1036_, v___x_1035_);
    return v___x_1037_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1038_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__20),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__20_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__20,
    );
    v___x_1039_ = l_Lake_KFacetConfig_kind__eq___autoParam___closed__4;
    v___x_1040_ = crate::leanh::lean_box(2);
    v___x_1041_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1041_, 0, v___x_1040_);
    crate::leanh::lean_ctor_set(v___x_1041_, 1, v___x_1039_);
    crate::leanh::lean_ctor_set(v___x_1041_, 2, v___x_1038_);
    return v___x_1041_;
}
pub unsafe fn _init_l_Lake_KFacetConfig_kind__eq___autoParam() -> *mut crate::leanh::LeanObject {
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1042_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__21),
        core::ptr::addr_of_mut!(l_Lake_KFacetConfig_kind__eq___autoParam___closed__21_once),
        _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__21,
    );
    return v___x_1042_;
}
pub unsafe fn l_Lake_FacetConfig_toKind___redArg(
    mut v_self_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_1043_);
    return v_self_1043_;
}
pub unsafe fn l_Lake_FacetConfig_toKind___redArg___boxed(
    mut v_self_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Lake_FacetConfig_toKind___redArg(v_self_1044_);
    crate::leanh::lean_dec_ref(v_self_1044_);
    return v_res_1045_;
}
pub unsafe fn l_Lake_FacetConfig_toKind(
    mut v_name_1046_: *mut crate::leanh::LeanObject,
    mut v_kind_1047_: *mut crate::leanh::LeanObject,
    mut v_self_1048_: *mut crate::leanh::LeanObject,
    mut v_h_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_self_1048_);
    return v_self_1048_;
}
pub unsafe fn l_Lake_FacetConfig_toKind___boxed(
    mut v_name_1050_: *mut crate::leanh::LeanObject,
    mut v_kind_1051_: *mut crate::leanh::LeanObject,
    mut v_self_1052_: *mut crate::leanh::LeanObject,
    mut v_h_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lake_FacetConfig_toKind(v_name_1050_, v_kind_1051_, v_self_1052_, v_h_1053_);
    crate::leanh::lean_dec_ref(v_self_1052_);
    crate::leanh::lean_dec(v_kind_1051_);
    crate::leanh::lean_dec(v_name_1050_);
    return v_res_1054_;
}
pub unsafe fn l_Lake_FacetConfig_toKind_x3f___redArg(
    mut v_kind_1055_: *mut crate::leanh::LeanObject,
    mut v_self_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    v_kind_1057_ = crate::leanh::lean_ctor_get(v_self_1056_, 0);
    v___x_1058_ = lean_name_eq(v_kind_1057_, v_kind_1055_);
    if v___x_1058_ == 0 {
        let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_self_1056_);
        v___x_1059_ = crate::leanh::lean_box(0);
        return v___x_1059_;
    } else {
        let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1060_, 0, v_self_1056_);
        return v___x_1060_;
    }
}
pub unsafe fn l_Lake_FacetConfig_toKind_x3f___redArg___boxed(
    mut v_kind_1061_: *mut crate::leanh::LeanObject,
    mut v_self_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1063_ = l_Lake_FacetConfig_toKind_x3f___redArg(v_kind_1061_, v_self_1062_);
    crate::leanh::lean_dec(v_kind_1061_);
    return v_res_1063_;
}
pub unsafe fn l_Lake_FacetConfig_toKind_x3f(
    mut v_name_1064_: *mut crate::leanh::LeanObject,
    mut v_kind_1065_: *mut crate::leanh::LeanObject,
    mut v_self_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lake_FacetConfig_toKind_x3f___redArg(v_kind_1065_, v_self_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lake_FacetConfig_toKind_x3f___boxed(
    mut v_name_1068_: *mut crate::leanh::LeanObject,
    mut v_kind_1069_: *mut crate::leanh::LeanObject,
    mut v_self_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1071_ = l_Lake_FacetConfig_toKind_x3f(v_name_1068_, v_kind_1069_, v_self_1070_);
    crate::leanh::lean_dec(v_kind_1069_);
    crate::leanh::lean_dec(v_name_1068_);
    return v_res_1071_;
}
pub unsafe fn l_Lake_KFacetConfig_run___redArg(
    mut v_self_1072_: *mut crate::leanh::LeanObject,
    mut v_info_1073_: *mut crate::leanh::LeanObject,
    mut v_a_1074_: *mut crate::leanh::LeanObject,
    mut v_a_1075_: *mut crate::leanh::LeanObject,
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_a_1078_: *mut crate::leanh::LeanObject,
    mut v_a_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fetchFn_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fetchFn_1081_ = crate::leanh::lean_ctor_get(v_self_1072_, 1);
    crate::leanh::lean_inc_ref(v_fetchFn_1081_);
    crate::leanh::lean_dec_ref(v_self_1072_);
    crate::leanh::lean_inc_ref(v_a_1078_);
    crate::leanh::lean_inc(v_a_1077_);
    crate::leanh::lean_inc(v_a_1076_);
    crate::leanh::lean_inc(v_a_1075_);
    v___x_1082_ = crate::leanh::lean_apply_8(
        v_fetchFn_1081_,
        v_info_1073_,
        v_a_1074_,
        v_a_1075_,
        v_a_1076_,
        v_a_1077_,
        v_a_1078_,
        v_a_1079_,
        crate::leanh::lean_box(0),
    );
    return v___x_1082_;
}
pub unsafe fn l_Lake_KFacetConfig_run___redArg___boxed(
    mut v_self_1083_: *mut crate::leanh::LeanObject,
    mut v_info_1084_: *mut crate::leanh::LeanObject,
    mut v_a_1085_: *mut crate::leanh::LeanObject,
    mut v_a_1086_: *mut crate::leanh::LeanObject,
    mut v_a_1087_: *mut crate::leanh::LeanObject,
    mut v_a_1088_: *mut crate::leanh::LeanObject,
    mut v_a_1089_: *mut crate::leanh::LeanObject,
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_a_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Lake_KFacetConfig_run___redArg(
        v_self_1083_,
        v_info_1084_,
        v_a_1085_,
        v_a_1086_,
        v_a_1087_,
        v_a_1088_,
        v_a_1089_,
        v_a_1090_,
    );
    crate::leanh::lean_dec_ref(v_a_1089_);
    crate::leanh::lean_dec(v_a_1088_);
    crate::leanh::lean_dec(v_a_1087_);
    crate::leanh::lean_dec(v_a_1086_);
    return v_res_1092_;
}
pub unsafe fn l_Lake_KFacetConfig_run(
    mut v_kind_1093_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1094_: *mut crate::leanh::LeanObject,
    mut v_facet_1095_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1096_: *mut crate::leanh::LeanObject,
    mut v_inst_1097_: *mut crate::leanh::LeanObject,
    mut v_inst_1098_: *mut crate::leanh::LeanObject,
    mut v_self_1099_: *mut crate::leanh::LeanObject,
    mut v_info_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
    mut v_a_1102_: *mut crate::leanh::LeanObject,
    mut v_a_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fetchFn_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fetchFn_1108_ = crate::leanh::lean_ctor_get(v_self_1099_, 1);
    crate::leanh::lean_inc_ref(v_fetchFn_1108_);
    crate::leanh::lean_dec_ref(v_self_1099_);
    crate::leanh::lean_inc_ref(v_a_1105_);
    crate::leanh::lean_inc(v_a_1104_);
    crate::leanh::lean_inc(v_a_1103_);
    crate::leanh::lean_inc(v_a_1102_);
    v___x_1109_ = crate::leanh::lean_apply_8(
        v_fetchFn_1108_,
        v_info_1100_,
        v_a_1101_,
        v_a_1102_,
        v_a_1103_,
        v_a_1104_,
        v_a_1105_,
        v_a_1106_,
        crate::leanh::lean_box(0),
    );
    return v___x_1109_;
}
pub unsafe fn l_Lake_KFacetConfig_run___boxed(
    mut v_kind_1110_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1111_: *mut crate::leanh::LeanObject,
    mut v_facet_1112_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1113_: *mut crate::leanh::LeanObject,
    mut v_inst_1114_: *mut crate::leanh::LeanObject,
    mut v_inst_1115_: *mut crate::leanh::LeanObject,
    mut v_self_1116_: *mut crate::leanh::LeanObject,
    mut v_info_1117_: *mut crate::leanh::LeanObject,
    mut v_a_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
    mut v_a_1123_: *mut crate::leanh::LeanObject,
    mut v_a_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ = l_Lake_KFacetConfig_run(
        v_kind_1110_,
        v_00_u03b1_1111_,
        v_facet_1112_,
        v_00_u03b2_1113_,
        v_inst_1114_,
        v_inst_1115_,
        v_self_1116_,
        v_info_1117_,
        v_a_1118_,
        v_a_1119_,
        v_a_1120_,
        v_a_1121_,
        v_a_1122_,
        v_a_1123_,
    );
    crate::leanh::lean_dec_ref(v_a_1122_);
    crate::leanh::lean_dec(v_a_1121_);
    crate::leanh::lean_dec(v_a_1120_);
    crate::leanh::lean_dec(v_a_1119_);
    crate::leanh::lean_dec(v_facet_1112_);
    crate::leanh::lean_dec(v_kind_1110_);
    return v_res_1125_;
}
pub unsafe fn l_Lake_mkFacetJobConfig___redArg(
    mut v_kind_1126_: *mut crate::leanh::LeanObject,
    mut v_inst_1127_: *mut crate::leanh::LeanObject,
    mut v_outKind_1128_: *mut crate::leanh::LeanObject,
    mut v_build_1129_: *mut crate::leanh::LeanObject,
    mut v_buildable_1130_: u8,
    mut v_memoize_1131_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = crate::leanh::lean_alloc_closure(
        l_Lake_formatQuery___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1132_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1132_, 1, v_inst_1127_);
    v___x_1133_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1133_, 0, v_kind_1126_);
    crate::leanh::lean_ctor_set(v___x_1133_, 1, v_build_1129_);
    crate::leanh::lean_ctor_set(v___x_1133_, 2, v_outKind_1128_);
    crate::leanh::lean_ctor_set(v___x_1133_, 3, v___x_1132_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1133_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v_buildable_1130_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1133_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v_memoize_1131_,
    );
    return v___x_1133_;
}
pub unsafe fn l_Lake_mkFacetJobConfig___redArg___boxed(
    mut v_kind_1134_: *mut crate::leanh::LeanObject,
    mut v_inst_1135_: *mut crate::leanh::LeanObject,
    mut v_outKind_1136_: *mut crate::leanh::LeanObject,
    mut v_build_1137_: *mut crate::leanh::LeanObject,
    mut v_buildable_1138_: *mut crate::leanh::LeanObject,
    mut v_memoize_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buildable_boxed_1140_: u8 = 0;
    let mut v_memoize_boxed_1141_: u8 = 0;
    let mut v_res_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buildable_boxed_1140_ = (crate::leanh::lean_unbox(v_buildable_1138_) as u8);
    v_memoize_boxed_1141_ = (crate::leanh::lean_unbox(v_memoize_1139_) as u8);
    v_res_1142_ = l_Lake_mkFacetJobConfig___redArg(
        v_kind_1134_,
        v_inst_1135_,
        v_outKind_1136_,
        v_build_1137_,
        v_buildable_boxed_1140_,
        v_memoize_boxed_1141_,
    );
    return v_res_1142_;
}
pub unsafe fn l_Lake_mkFacetJobConfig(
    mut v_00_u03b2_1143_: *mut crate::leanh::LeanObject,
    mut v_kind_1144_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1145_: *mut crate::leanh::LeanObject,
    mut v_facet_1146_: *mut crate::leanh::LeanObject,
    mut v_inst_1147_: *mut crate::leanh::LeanObject,
    mut v_outKind_1148_: *mut crate::leanh::LeanObject,
    mut v_i_1149_: *mut crate::leanh::LeanObject,
    mut v_o_1150_: *mut crate::leanh::LeanObject,
    mut v_build_1151_: *mut crate::leanh::LeanObject,
    mut v_buildable_1152_: u8,
    mut v_memoize_1153_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1154_ = crate::leanh::lean_alloc_closure(
        l_Lake_formatQuery___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1154_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1154_, 1, v_inst_1147_);
    v___x_1155_ = crate::leanh::lean_alloc_ctor(0, 4, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1155_, 0, v_kind_1144_);
    crate::leanh::lean_ctor_set(v___x_1155_, 1, v_build_1151_);
    crate::leanh::lean_ctor_set(v___x_1155_, 2, v_outKind_1148_);
    crate::leanh::lean_ctor_set(v___x_1155_, 3, v___x_1154_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1155_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
        v_buildable_1152_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1155_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 1) as u32,
        v_memoize_1153_,
    );
    return v___x_1155_;
}
pub unsafe fn l_Lake_mkFacetJobConfig___boxed(
    mut v_00_u03b2_1156_: *mut crate::leanh::LeanObject,
    mut v_kind_1157_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1158_: *mut crate::leanh::LeanObject,
    mut v_facet_1159_: *mut crate::leanh::LeanObject,
    mut v_inst_1160_: *mut crate::leanh::LeanObject,
    mut v_outKind_1161_: *mut crate::leanh::LeanObject,
    mut v_i_1162_: *mut crate::leanh::LeanObject,
    mut v_o_1163_: *mut crate::leanh::LeanObject,
    mut v_build_1164_: *mut crate::leanh::LeanObject,
    mut v_buildable_1165_: *mut crate::leanh::LeanObject,
    mut v_memoize_1166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buildable_boxed_1167_: u8 = 0;
    let mut v_memoize_boxed_1168_: u8 = 0;
    let mut v_res_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buildable_boxed_1167_ = (crate::leanh::lean_unbox(v_buildable_1165_) as u8);
    v_memoize_boxed_1168_ = (crate::leanh::lean_unbox(v_memoize_1166_) as u8);
    v_res_1169_ = l_Lake_mkFacetJobConfig(
        v_00_u03b2_1156_,
        v_kind_1157_,
        v_00_u03b1_1158_,
        v_facet_1159_,
        v_inst_1160_,
        v_outKind_1161_,
        v_i_1162_,
        v_o_1163_,
        v_build_1164_,
        v_buildable_boxed_1167_,
        v_memoize_boxed_1168_,
    );
    crate::leanh::lean_dec(v_facet_1159_);
    return v_res_1169_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Config_FacetConfig(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Config_FacetConfig(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    l_Lake_KFacetConfig_kind__eq___autoParam = _init_l_Lake_KFacetConfig_kind__eq___autoParam();
    crate::leanh::lean_mark_persistent(l_Lake_KFacetConfig_kind__eq___autoParam);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Config_FacetConfig(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Build_Fetch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_FacetConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Config_FacetConfig(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Config_FacetConfig(builtin);
}
