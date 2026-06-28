// Lean compiler output
// Module: Lean.Elab.ErrorUtils
// Imports: Lean.Message
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Lean::Message::{
    initialize_Lean_Message, l_Lean_MessageData_nil, l_Lean_MessageData_ofFormat,
    l_Lean_stringToMessageData, runtime_initialize_Lean_Message,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mod};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [114, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [110, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 101, 110, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [110, 105, 110, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 105, 103, 104, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 101, 118, 101, 110, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [115, 105, 120, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 105, 102, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [102, 111, 117, 114, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 104, 105, 114, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 101, 99, 111, 110, 100, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12_value: LeanStringObject<
    6,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 105, 114, 115, 116, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [122, 101, 114, 111, 116, 104, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value:
    LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 97, 110, 100, 32, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [44, 32, 97, 110, 100, 32, 0],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4_value:
    LeanCtorObject<4> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value
        ) as *mut LeanObject,
    ],
};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4_value
) as *mut LeanObject;
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__4_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__1_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__3_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [115, 0]};
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsString___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1_value
) as *mut LeanObject;
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___closed__1_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal(
    mut v_x_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: u8 = 0;
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_193_: u8 = 0;
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: u8 = 0;
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: u8 = 0;
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: u8 = 0;
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: u8 = 0;
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: u8 = 0;
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: u8 = 0;
    let mut v___x_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: u8 = 0;
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_209_: u8 = 0;
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_212_: u8 = 0;
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: u8 = 0;
    let mut v___x_215_: u8 = 0;
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: u8 = 0;
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: u8 = 0;
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: u8 = 0;
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_190_ = lean_unsigned_to_nat(0);
                v___x_191_ = lean_nat_dec_eq(v_x_189_, v___x_190_);
                if v___x_191_ == 0 {
                    v___x_192_ = lean_unsigned_to_nat(1);
                    v___x_193_ = lean_nat_dec_eq(v_x_189_, v___x_192_);
                    if v___x_193_ == 0 {
                        v___x_194_ = lean_unsigned_to_nat(2);
                        v___x_195_ = lean_nat_dec_eq(v_x_189_, v___x_194_);
                        if v___x_195_ == 0 {
                            v___x_196_ = lean_unsigned_to_nat(3);
                            v___x_197_ = lean_nat_dec_eq(v_x_189_, v___x_196_);
                            if v___x_197_ == 0 {
                                v___x_198_ = lean_unsigned_to_nat(4);
                                v___x_199_ = lean_nat_dec_eq(v_x_189_, v___x_198_);
                                if v___x_199_ == 0 {
                                    v___x_200_ = lean_unsigned_to_nat(5);
                                    v___x_201_ = lean_nat_dec_eq(v_x_189_, v___x_200_);
                                    if v___x_201_ == 0 {
                                        v___x_202_ = lean_unsigned_to_nat(6);
                                        v___x_203_ = lean_nat_dec_eq(v_x_189_, v___x_202_);
                                        if v___x_203_ == 0 {
                                            v___x_204_ = lean_unsigned_to_nat(7);
                                            v___x_205_ = lean_nat_dec_eq(v_x_189_, v___x_204_);
                                            if v___x_205_ == 0 {
                                                v___x_206_ = lean_unsigned_to_nat(8);
                                                v___x_207_ = lean_nat_dec_eq(v_x_189_, v___x_206_);
                                                if v___x_207_ == 0 {
                                                    v___x_208_ = lean_unsigned_to_nat(9);
                                                    v___x_209_ =
                                                        lean_nat_dec_eq(v_x_189_, v___x_208_);
                                                    if v___x_209_ == 0 {
                                                        v___x_210_ = lean_unsigned_to_nat(10);
                                                        v___x_228_ =
                                                            lean_nat_dec_eq(v_x_189_, v___x_210_);
                                                        if v___x_228_ == 0 {
                                                            v___x_229_ = lean_unsigned_to_nat(100);
                                                            v___x_230_ =
                                                                lean_nat_mod(v_x_189_, v___x_229_);
                                                            v___x_231_ = lean_nat_dec_lt(
                                                                v___x_210_, v___x_230_,
                                                            );
                                                            if v___x_231_ == 0 {
                                                                lean_dec(v___x_230_);
                                                                v___y_212_ = v___x_231_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_232_ =
                                                                    lean_unsigned_to_nat(20);
                                                                v___x_233_ = lean_nat_dec_lt(
                                                                    v___x_230_, v___x_232_,
                                                                );
                                                                lean_dec(v___x_230_);
                                                                v___y_212_ = v___x_233_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v_x_189_);
                                                            v___x_234_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__3;
                                                            return v___x_234_;
                                                        }
                                                    } else {
                                                        lean_dec(v_x_189_);
                                                        v___x_235_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__4;
                                                        return v___x_235_;
                                                    }
                                                } else {
                                                    lean_dec(v_x_189_);
                                                    v___x_236_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__5;
                                                    return v___x_236_;
                                                }
                                            } else {
                                                lean_dec(v_x_189_);
                                                v___x_237_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__6;
                                                return v___x_237_;
                                            }
                                        } else {
                                            lean_dec(v_x_189_);
                                            v___x_238_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__7;
                                            return v___x_238_;
                                        }
                                    } else {
                                        lean_dec(v_x_189_);
                                        v___x_239_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__8;
                                        return v___x_239_;
                                    }
                                } else {
                                    lean_dec(v_x_189_);
                                    v___x_240_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__9;
                                    return v___x_240_;
                                }
                            } else {
                                lean_dec(v_x_189_);
                                v___x_241_ =
                                    l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__10;
                                return v___x_241_;
                            }
                        } else {
                            lean_dec(v_x_189_);
                            v___x_242_ =
                                l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__11;
                            return v___x_242_;
                        }
                    } else {
                        lean_dec(v_x_189_);
                        v___x_243_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__12;
                        return v___x_243_;
                    }
                } else {
                    lean_dec(v_x_189_);
                    v___x_244_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__13;
                    return v___x_244_;
                }
            }
            1 => {
                if v___y_212_ == 0 {
                    v___x_213_ = lean_nat_mod(v_x_189_, v___x_210_);
                    v___x_214_ = lean_nat_dec_eq(v___x_213_, v___x_194_);
                    if v___x_214_ == 0 {
                        v___x_215_ = lean_nat_dec_eq(v___x_213_, v___x_196_);
                        lean_dec(v___x_213_);
                        if v___x_215_ == 0 {
                            v___x_216_ = l_Nat_reprFast(v_x_189_);
                            v___x_217_ =
                                l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0;
                            v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
                            return v___x_218_;
                        } else {
                            v___x_219_ = l_Nat_reprFast(v_x_189_);
                            v___x_220_ =
                                l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__1;
                            v___x_221_ = lean_string_append(v___x_219_, v___x_220_);
                            return v___x_221_;
                        }
                    } else {
                        lean_dec(v___x_213_);
                        v___x_222_ = l_Nat_reprFast(v_x_189_);
                        v___x_223_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__2;
                        v___x_224_ = lean_string_append(v___x_222_, v___x_223_);
                        return v___x_224_;
                    }
                } else {
                    v___x_225_ = l_Nat_reprFast(v_x_189_);
                    v___x_226_ = l___private_Lean_Elab_ErrorUtils_0__Nat_toOrdinal___closed__0;
                    v___x_227_ = lean_string_append(v___x_225_, v___x_226_);
                    return v___x_227_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1()
-> *mut LeanObject {
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    v___x_257_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__0;
    v___x_258_ = l_Lean_MessageData_ofFormat(v___x_257_);
    return v___x_258_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3()
-> *mut LeanObject {
    let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    v___x_261_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__2;
    v___x_262_ = l_Lean_MessageData_ofFormat(v___x_261_);
    return v___x_262_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5()
-> *mut LeanObject {
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_265_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__4;
    v___x_266_ = l_Lean_MessageData_ofFormat(v___x_265_);
    return v___x_266_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7()
-> *mut LeanObject {
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    v___x_269_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__6;
    v___x_270_ = l_Lean_MessageData_ofFormat(v___x_269_);
    return v___x_270_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8()
-> *mut LeanObject {
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    v___x_271_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__7);
    v___x_272_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__5);
    v___x_273_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__3);
    v___x_274_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__1);
    v___x_275_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_275_, 0, v___x_274_);
    lean_ctor_set(v___x_275_, 1, v___x_273_);
    lean_ctor_set(v___x_275_, 2, v___x_272_);
    lean_ctor_set(v___x_275_, 3, v___x_271_);
    return v___x_275_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData()
-> *mut LeanObject {
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    v___x_276_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData___closed__8);
    return v___x_276_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__List_toOxford___redArg(
    mut v_inst_277_: *mut LeanObject,
    mut v_inst_278_: *mut LeanObject,
    mut v_x_279_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_279_) == 0 {
        let mut v_emp_280_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_inst_277_);
        v_emp_280_ = lean_ctor_get(v_inst_278_, 0);
        lean_inc(v_emp_280_);
        lean_dec_ref(v_inst_278_);
        return v_emp_280_;
    } else {
        let mut v_tail_281_: *mut LeanObject = core::ptr::null_mut();
        v_tail_281_ = lean_ctor_get(v_x_279_, 1);
        if lean_obj_tag(v_tail_281_) == 0 {
            let mut v_head_282_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_278_);
            lean_dec(v_inst_277_);
            v_head_282_ = lean_ctor_get(v_x_279_, 0);
            lean_inc(v_head_282_);
            lean_dec_ref_known(v_x_279_, 2);
            return v_head_282_;
        } else {
            let mut v_tail_283_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_tail_281_);
            v_tail_283_ = lean_ctor_get(v_tail_281_, 1);
            if lean_obj_tag(v_tail_283_) == 0 {
                let mut v_head_284_: *mut LeanObject = core::ptr::null_mut();
                let mut v_head_285_: *mut LeanObject = core::ptr::null_mut();
                let mut v_and_286_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
                v_head_284_ = lean_ctor_get(v_x_279_, 0);
                lean_inc(v_head_284_);
                lean_dec_ref_known(v_x_279_, 2);
                v_head_285_ = lean_ctor_get(v_tail_281_, 0);
                lean_inc(v_head_285_);
                lean_dec_ref_known(v_tail_281_, 2);
                v_and_286_ = lean_ctor_get(v_inst_278_, 1);
                lean_inc(v_and_286_);
                lean_dec_ref(v_inst_278_);
                lean_inc(v_inst_277_);
                v___x_287_ = lean_apply_2(v_inst_277_, v_head_284_, v_and_286_);
                v___x_288_ = lean_apply_2(v_inst_277_, v___x_287_, v_head_285_);
                return v___x_288_;
            } else {
                let mut v_tail_289_: *mut LeanObject = core::ptr::null_mut();
                v_tail_289_ = lean_ctor_get(v_tail_283_, 1);
                if lean_obj_tag(v_tail_289_) == 0 {
                    let mut v_head_290_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_head_291_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_head_292_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_comma_293_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_commaAnd_294_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
                    lean_inc_ref(v_tail_283_);
                    v_head_290_ = lean_ctor_get(v_x_279_, 0);
                    lean_inc(v_head_290_);
                    lean_dec_ref_known(v_x_279_, 2);
                    v_head_291_ = lean_ctor_get(v_tail_281_, 0);
                    lean_inc(v_head_291_);
                    lean_dec_ref_known(v_tail_281_, 2);
                    v_head_292_ = lean_ctor_get(v_tail_283_, 0);
                    lean_inc(v_head_292_);
                    lean_dec_ref_known(v_tail_283_, 2);
                    v_comma_293_ = lean_ctor_get(v_inst_278_, 2);
                    lean_inc(v_comma_293_);
                    v_commaAnd_294_ = lean_ctor_get(v_inst_278_, 3);
                    lean_inc(v_commaAnd_294_);
                    lean_dec_ref(v_inst_278_);
                    lean_inc_n(v_inst_277_, 3);
                    v___x_295_ = lean_apply_2(v_inst_277_, v_head_290_, v_comma_293_);
                    v___x_296_ = lean_apply_2(v_inst_277_, v___x_295_, v_head_291_);
                    v___x_297_ = lean_apply_2(v_inst_277_, v___x_296_, v_commaAnd_294_);
                    v___x_298_ = lean_apply_2(v_inst_277_, v___x_297_, v_head_292_);
                    return v___x_298_;
                } else {
                    let mut v_head_299_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_comma_300_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
                    v_head_299_ = lean_ctor_get(v_x_279_, 0);
                    lean_inc(v_head_299_);
                    lean_dec_ref_known(v_x_279_, 2);
                    v_comma_300_ = lean_ctor_get(v_inst_278_, 2);
                    lean_inc_n(v_inst_277_, 2);
                    lean_inc(v_comma_300_);
                    v___x_301_ = lean_apply_2(v_inst_277_, v_head_299_, v_comma_300_);
                    v___x_302_ = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___redArg(
                        v_inst_277_,
                        v_inst_278_,
                        v_tail_281_,
                    );
                    v___x_303_ = lean_apply_2(v_inst_277_, v___x_301_, v___x_302_);
                    return v___x_303_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__List_toOxford(
    mut v_00_u03b1_304_: *mut LeanObject,
    mut v_inst_305_: *mut LeanObject,
    mut v_inst_306_: *mut LeanObject,
    mut v_x_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    v___x_308_ = l___private_Lean_Elab_ErrorUtils_0__List_toOxford___redArg(
        v_inst_305_,
        v_inst_306_,
        v_x_307_,
    );
    return v___x_308_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0(
    mut v_x_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    v___x_311_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0;
    v___x_312_ = lean_string_append(v_x_310_, v___x_311_);
    return v___x_312_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    v___x_318_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsString___lam__0___closed__0;
    v___x_319_ = l_Lean_stringToMessageData(v___x_318_);
    return v___x_319_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0(
    mut v_x_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    v___x_321_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___lam__0___closed__0);
    v___x_322_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_322_, 0, v_x_320_);
    lean_ctor_set(v___x_322_, 1, v___x_321_);
    return v___x_322_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1()
-> *mut LeanObject {
    let mut v___f_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    v___f_324_ =
        l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__0;
    v___x_325_ = l_Lean_MessageData_nil;
    v___x_326_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_326_, 0, v___x_325_);
    lean_ctor_set(v___x_326_, 1, v___f_324_);
    return v___x_326_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData()
-> *mut LeanObject {
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    v___x_327_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1_once), _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData___closed__1);
    return v___x_327_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg(
    mut v_count_328_: *mut LeanObject,
    mut v_singular_329_: *mut LeanObject,
    mut v_plural_330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: u8 = 0;
    v___x_331_ = lean_unsigned_to_nat(1);
    v___x_332_ = lean_nat_dec_eq(v_count_328_, v___x_331_);
    if v___x_332_ == 0 {
        lean_inc(v_plural_330_);
        return v_plural_330_;
    } else {
        lean_inc(v_singular_329_);
        return v_singular_329_;
    }
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg___boxed(
    mut v_count_333_: *mut LeanObject,
    mut v_singular_334_: *mut LeanObject,
    mut v_plural_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_336_: *mut LeanObject = core::ptr::null_mut();
    v_res_336_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg(
        v_count_333_,
        v_singular_334_,
        v_plural_335_,
    );
    lean_dec(v_plural_335_);
    lean_dec(v_singular_334_);
    lean_dec(v_count_333_);
    return v_res_336_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural(
    mut v_00_u03b1_337_: *mut LeanObject,
    mut v_inst_338_: *mut LeanObject,
    mut v_count_339_: *mut LeanObject,
    mut v_singular_340_: *mut LeanObject,
    mut v_plural_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    v___x_342_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural___redArg(
        v_count_339_,
        v_singular_340_,
        v_plural_341_,
    );
    return v___x_342_;
}
pub unsafe fn l___private_Lean_Elab_ErrorUtils_0__Nat_plural___boxed(
    mut v_00_u03b1_343_: *mut LeanObject,
    mut v_inst_344_: *mut LeanObject,
    mut v_count_345_: *mut LeanObject,
    mut v_singular_346_: *mut LeanObject,
    mut v_plural_347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_348_: *mut LeanObject = core::ptr::null_mut();
    v_res_348_ = l___private_Lean_Elab_ErrorUtils_0__Nat_plural(
        v_00_u03b1_343_,
        v_inst_344_,
        v_count_345_,
        v_singular_346_,
        v_plural_347_,
    );
    lean_dec(v_plural_347_);
    lean_dec(v_singular_346_);
    lean_dec(v_count_345_);
    lean_dec_ref(v_inst_344_);
    return v_res_348_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ErrorUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData =
        _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData();
    lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasOxfordStringsMessageData);
    l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData =
        _init_l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData();
    lean_mark_persistent(l___private_Lean_Elab_ErrorUtils_0__Lean_instHasPluralDefaultsMessageData);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ErrorUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ErrorUtils(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ErrorUtils(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ErrorUtils(builtin);
}
