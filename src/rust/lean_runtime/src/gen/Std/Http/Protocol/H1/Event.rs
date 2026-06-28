// Lean compiler output
// Module: Std.Http.Protocol.H1.Event
// Imports: Std.Time Std.Http.Data Std.Http.Internal Std.Http.Protocol.H1.Parser Std.Http.Protocol.H1.Config Std.Http.Protocol.H1.Message Std.Http.Protocol.H1.Error
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Std::Http::Data::{initialize_Std_Http_Data, runtime_initialize_Std_Http_Data};
use crate::r#gen::Std::Http::Internal::{
    initialize_Std_Http_Internal, runtime_initialize_Std_Http_Internal,
};
use crate::r#gen::Std::Http::Protocol::H1::Config::{
    initialize_Std_Http_Protocol_H1_Config, runtime_initialize_Std_Http_Protocol_H1_Config,
};
use crate::r#gen::Std::Http::Protocol::H1::Error::{
    initialize_Std_Http_Protocol_H1_Error, l_Std_Http_Protocol_H1_instReprError_repr,
    runtime_initialize_Std_Http_Protocol_H1_Error,
};
use crate::r#gen::Std::Http::Protocol::H1::Message::{
    initialize_Std_Http_Protocol_H1_Message, l_Std_Http_Protocol_H1_instReprHead,
    runtime_initialize_Std_Http_Protocol_H1_Message,
};
use crate::r#gen::Std::Http::Protocol::H1::Parser::{
    initialize_Std_Http_Protocol_H1_Parser, runtime_initialize_Std_Http_Protocol_H1_Parser,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::lean_nat_dec_le;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0_value)
        as *mut LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__2_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 99, 108, 111, 115, 101, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value: LeanStringObject<37> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 37,
        m_capacity: 37,
        m_length: 36,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 99, 108, 111, 115, 101, 66, 111, 100, 121, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 110, 101, 101, 100, 65, 110, 115, 119, 101, 114, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 110, 101, 120, 116, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 99, 111, 110, 116, 105, 110, 117, 101, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 101, 110, 100, 72, 101, 97, 100, 101, 114, 115, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__11_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12_value)
        as *mut LeanObject;
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 110, 101, 101, 100, 77, 111, 114, 101, 68, 97, 116,
            97, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__16_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value: LeanStringObject<34> =
    LeanStringObject {
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
            83, 116, 100, 46, 72, 116, 116, 112, 46, 80, 114, 111, 116, 111, 99, 111, 108, 46, 72,
            49, 46, 69, 118, 101, 110, 116, 46, 102, 97, 105, 108, 101, 100, 0,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__18_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__19_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(
    mut v_x_358_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_358_) {
        0 => {
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            v___x_359_ = lean_unsigned_to_nat(0);
            return v___x_359_;
        }
        1 => {
            let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
            v___x_360_ = lean_unsigned_to_nat(1);
            return v___x_360_;
        }
        2 => {
            let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
            v___x_361_ = lean_unsigned_to_nat(2);
            return v___x_361_;
        }
        3 => {
            let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
            v___x_362_ = lean_unsigned_to_nat(3);
            return v___x_362_;
        }
        4 => {
            let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
            v___x_363_ = lean_unsigned_to_nat(4);
            return v___x_363_;
        }
        5 => {
            let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
            v___x_364_ = lean_unsigned_to_nat(5);
            return v___x_364_;
        }
        6 => {
            let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
            v___x_365_ = lean_unsigned_to_nat(6);
            return v___x_365_;
        }
        _ => {
            let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
            v___x_366_ = lean_unsigned_to_nat(7);
            return v___x_366_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx___redArg___boxed(
    mut v_x_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_368_: *mut LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(v_x_367_);
    lean_dec(v_x_367_);
    return v_res_368_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx(
    mut v_dir_369_: u8,
    mut v_x_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    v___x_371_ = l_Std_Http_Protocol_H1_Event_ctorIdx___redArg(v_x_370_);
    return v___x_371_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorIdx___boxed(
    mut v_dir_372_: *mut LeanObject,
    mut v_x_373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_374_: u8 = 0;
    let mut v_res_375_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_374_ = (lean_unbox(v_dir_372_) as u8);
    v_res_375_ = l_Std_Http_Protocol_H1_Event_ctorIdx(v_dir_boxed_374_, v_x_373_);
    lean_dec(v_x_373_);
    return v_res_375_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorElim___redArg(
    mut v_t_376_: *mut LeanObject,
    mut v_k_377_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_376_) {
        0 => {
            let mut v_head_378_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
            v_head_378_ = lean_ctor_get(v_t_376_, 0);
            lean_inc(v_head_378_);
            lean_dec_ref_known(v_t_376_, 1);
            v___x_379_ = lean_apply_1(v_k_377_, v_head_378_);
            return v___x_379_;
        }
        1 => {
            let mut v_size_380_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
            v_size_380_ = lean_ctor_get(v_t_376_, 0);
            lean_inc(v_size_380_);
            lean_dec_ref_known(v_t_376_, 1);
            v___x_381_ = lean_apply_1(v_k_377_, v_size_380_);
            return v___x_381_;
        }
        2 => {
            let mut v_err_382_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
            v_err_382_ = lean_ctor_get(v_t_376_, 0);
            lean_inc(v_err_382_);
            lean_dec_ref_known(v_t_376_, 1);
            v___x_383_ = lean_apply_1(v_k_377_, v_err_382_);
            return v___x_383_;
        }
        _ => {
            lean_dec(v_t_376_);
            return v_k_377_;
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorElim(
    mut v_dir_384_: u8,
    mut v_motive_385_: *mut LeanObject,
    mut v_ctorIdx_386_: *mut LeanObject,
    mut v_t_387_: *mut LeanObject,
    mut v_h_388_: *mut LeanObject,
    mut v_k_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_387_, v_k_389_);
    return v___x_390_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_ctorElim___boxed(
    mut v_dir_391_: *mut LeanObject,
    mut v_motive_392_: *mut LeanObject,
    mut v_ctorIdx_393_: *mut LeanObject,
    mut v_t_394_: *mut LeanObject,
    mut v_h_395_: *mut LeanObject,
    mut v_k_396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_397_: u8 = 0;
    let mut v_res_398_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_397_ = (lean_unbox(v_dir_391_) as u8);
    v_res_398_ = l_Std_Http_Protocol_H1_Event_ctorElim(
        v_dir_boxed_397_,
        v_motive_392_,
        v_ctorIdx_393_,
        v_t_394_,
        v_h_395_,
        v_k_396_,
    );
    lean_dec(v_ctorIdx_393_);
    return v_res_398_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_endHeaders_elim___redArg(
    mut v_t_399_: *mut LeanObject,
    mut v_endHeaders_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_401_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_399_, v_endHeaders_400_);
    return v___x_401_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_endHeaders_elim(
    mut v_dir_402_: u8,
    mut v_motive_403_: *mut LeanObject,
    mut v_t_404_: *mut LeanObject,
    mut v_h_405_: *mut LeanObject,
    mut v_endHeaders_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    v___x_407_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_404_, v_endHeaders_406_);
    return v___x_407_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_endHeaders_elim___boxed(
    mut v_dir_408_: *mut LeanObject,
    mut v_motive_409_: *mut LeanObject,
    mut v_t_410_: *mut LeanObject,
    mut v_h_411_: *mut LeanObject,
    mut v_endHeaders_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_413_: u8 = 0;
    let mut v_res_414_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_413_ = (lean_unbox(v_dir_408_) as u8);
    v_res_414_ = l_Std_Http_Protocol_H1_Event_endHeaders_elim(
        v_dir_boxed_413_,
        v_motive_409_,
        v_t_410_,
        v_h_411_,
        v_endHeaders_412_,
    );
    return v_res_414_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needMoreData_elim___redArg(
    mut v_t_415_: *mut LeanObject,
    mut v_needMoreData_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    v___x_417_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_415_, v_needMoreData_416_);
    return v___x_417_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needMoreData_elim(
    mut v_dir_418_: u8,
    mut v_motive_419_: *mut LeanObject,
    mut v_t_420_: *mut LeanObject,
    mut v_h_421_: *mut LeanObject,
    mut v_needMoreData_422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    v___x_423_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_420_, v_needMoreData_422_);
    return v___x_423_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needMoreData_elim___boxed(
    mut v_dir_424_: *mut LeanObject,
    mut v_motive_425_: *mut LeanObject,
    mut v_t_426_: *mut LeanObject,
    mut v_h_427_: *mut LeanObject,
    mut v_needMoreData_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_429_: u8 = 0;
    let mut v_res_430_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_429_ = (lean_unbox(v_dir_424_) as u8);
    v_res_430_ = l_Std_Http_Protocol_H1_Event_needMoreData_elim(
        v_dir_boxed_429_,
        v_motive_425_,
        v_t_426_,
        v_h_427_,
        v_needMoreData_428_,
    );
    return v_res_430_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_failed_elim___redArg(
    mut v_t_431_: *mut LeanObject,
    mut v_failed_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    v___x_433_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_431_, v_failed_432_);
    return v___x_433_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_failed_elim(
    mut v_dir_434_: u8,
    mut v_motive_435_: *mut LeanObject,
    mut v_t_436_: *mut LeanObject,
    mut v_h_437_: *mut LeanObject,
    mut v_failed_438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    v___x_439_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_436_, v_failed_438_);
    return v___x_439_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_failed_elim___boxed(
    mut v_dir_440_: *mut LeanObject,
    mut v_motive_441_: *mut LeanObject,
    mut v_t_442_: *mut LeanObject,
    mut v_h_443_: *mut LeanObject,
    mut v_failed_444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_445_: u8 = 0;
    let mut v_res_446_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_445_ = (lean_unbox(v_dir_440_) as u8);
    v_res_446_ = l_Std_Http_Protocol_H1_Event_failed_elim(
        v_dir_boxed_445_,
        v_motive_441_,
        v_t_442_,
        v_h_443_,
        v_failed_444_,
    );
    return v_res_446_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_close_elim___redArg(
    mut v_t_447_: *mut LeanObject,
    mut v_close_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    v___x_449_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_447_, v_close_448_);
    return v___x_449_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_close_elim(
    mut v_dir_450_: u8,
    mut v_motive_451_: *mut LeanObject,
    mut v_t_452_: *mut LeanObject,
    mut v_h_453_: *mut LeanObject,
    mut v_close_454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v___x_455_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_452_, v_close_454_);
    return v___x_455_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_close_elim___boxed(
    mut v_dir_456_: *mut LeanObject,
    mut v_motive_457_: *mut LeanObject,
    mut v_t_458_: *mut LeanObject,
    mut v_h_459_: *mut LeanObject,
    mut v_close_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_461_: u8 = 0;
    let mut v_res_462_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_461_ = (lean_unbox(v_dir_456_) as u8);
    v_res_462_ = l_Std_Http_Protocol_H1_Event_close_elim(
        v_dir_boxed_461_,
        v_motive_457_,
        v_t_458_,
        v_h_459_,
        v_close_460_,
    );
    return v_res_462_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_closeBody_elim___redArg(
    mut v_t_463_: *mut LeanObject,
    mut v_closeBody_464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    v___x_465_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_463_, v_closeBody_464_);
    return v___x_465_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_closeBody_elim(
    mut v_dir_466_: u8,
    mut v_motive_467_: *mut LeanObject,
    mut v_t_468_: *mut LeanObject,
    mut v_h_469_: *mut LeanObject,
    mut v_closeBody_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    v___x_471_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_468_, v_closeBody_470_);
    return v___x_471_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_closeBody_elim___boxed(
    mut v_dir_472_: *mut LeanObject,
    mut v_motive_473_: *mut LeanObject,
    mut v_t_474_: *mut LeanObject,
    mut v_h_475_: *mut LeanObject,
    mut v_closeBody_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_477_: u8 = 0;
    let mut v_res_478_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_477_ = (lean_unbox(v_dir_472_) as u8);
    v_res_478_ = l_Std_Http_Protocol_H1_Event_closeBody_elim(
        v_dir_boxed_477_,
        v_motive_473_,
        v_t_474_,
        v_h_475_,
        v_closeBody_476_,
    );
    return v_res_478_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needAnswer_elim___redArg(
    mut v_t_479_: *mut LeanObject,
    mut v_needAnswer_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_481_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_479_, v_needAnswer_480_);
    return v___x_481_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needAnswer_elim(
    mut v_dir_482_: u8,
    mut v_motive_483_: *mut LeanObject,
    mut v_t_484_: *mut LeanObject,
    mut v_h_485_: *mut LeanObject,
    mut v_needAnswer_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_487_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_484_, v_needAnswer_486_);
    return v___x_487_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_needAnswer_elim___boxed(
    mut v_dir_488_: *mut LeanObject,
    mut v_motive_489_: *mut LeanObject,
    mut v_t_490_: *mut LeanObject,
    mut v_h_491_: *mut LeanObject,
    mut v_needAnswer_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_493_: u8 = 0;
    let mut v_res_494_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_493_ = (lean_unbox(v_dir_488_) as u8);
    v_res_494_ = l_Std_Http_Protocol_H1_Event_needAnswer_elim(
        v_dir_boxed_493_,
        v_motive_489_,
        v_t_490_,
        v_h_491_,
        v_needAnswer_492_,
    );
    return v_res_494_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_next_elim___redArg(
    mut v_t_495_: *mut LeanObject,
    mut v_next_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    v___x_497_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_495_, v_next_496_);
    return v___x_497_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_next_elim(
    mut v_dir_498_: u8,
    mut v_motive_499_: *mut LeanObject,
    mut v_t_500_: *mut LeanObject,
    mut v_h_501_: *mut LeanObject,
    mut v_next_502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    v___x_503_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_500_, v_next_502_);
    return v___x_503_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_next_elim___boxed(
    mut v_dir_504_: *mut LeanObject,
    mut v_motive_505_: *mut LeanObject,
    mut v_t_506_: *mut LeanObject,
    mut v_h_507_: *mut LeanObject,
    mut v_next_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_509_: u8 = 0;
    let mut v_res_510_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_509_ = (lean_unbox(v_dir_504_) as u8);
    v_res_510_ = l_Std_Http_Protocol_H1_Event_next_elim(
        v_dir_boxed_509_,
        v_motive_505_,
        v_t_506_,
        v_h_507_,
        v_next_508_,
    );
    return v_res_510_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_continue_elim___redArg(
    mut v_t_511_: *mut LeanObject,
    mut v_continue_512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    v___x_513_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_511_, v_continue_512_);
    return v___x_513_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_continue_elim(
    mut v_dir_514_: u8,
    mut v_motive_515_: *mut LeanObject,
    mut v_t_516_: *mut LeanObject,
    mut v_h_517_: *mut LeanObject,
    mut v_continue_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    v___x_519_ = l_Std_Http_Protocol_H1_Event_ctorElim___redArg(v_t_516_, v_continue_518_);
    return v___x_519_;
}
pub unsafe fn l_Std_Http_Protocol_H1_Event_continue_elim___boxed(
    mut v_dir_520_: *mut LeanObject,
    mut v_motive_521_: *mut LeanObject,
    mut v_t_522_: *mut LeanObject,
    mut v_h_523_: *mut LeanObject,
    mut v_continue_524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_525_: u8 = 0;
    let mut v_res_526_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_525_ = (lean_unbox(v_dir_520_) as u8);
    v_res_526_ = l_Std_Http_Protocol_H1_Event_continue_elim(
        v_dir_boxed_525_,
        v_motive_521_,
        v_t_522_,
        v_h_523_,
        v_continue_524_,
    );
    return v_res_526_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent_default(
    mut v_dir_529_: u8,
) -> *mut LeanObject {
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    v___x_530_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default___closed__0;
    return v___x_530_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent_default___boxed(
    mut v_dir_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_boxed_532_: u8 = 0;
    let mut v_res_533_: *mut LeanObject = core::ptr::null_mut();
    v_dir_boxed_532_ = (lean_unbox(v_dir_531_) as u8);
    v_res_533_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_dir_boxed_532_);
    return v_res_533_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent(mut v_a_534_: u8) -> *mut LeanObject {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    v___x_535_ = l_Std_Http_Protocol_H1_instInhabitedEvent_default(v_a_534_);
    return v___x_535_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instInhabitedEvent___boxed(
    mut v_a_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5__boxed_537_: u8 = 0;
    let mut v_res_538_: *mut LeanObject = core::ptr::null_mut();
    v_a_5__boxed_537_ = (lean_unbox(v_a_536_) as u8);
    v_res_538_ = l_Std_Http_Protocol_H1_instInhabitedEvent(v_a_5__boxed_537_);
    return v_res_538_;
}
pub unsafe fn l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(
    mut v_x_545_: *mut LeanObject,
    mut v_x_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_545_) == 0 {
                    v___x_547_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__1;
                    return v___x_547_;
                } else {
                    v_val_548_ = lean_ctor_get(v_x_545_, 0);
                    v_isSharedCheck_559_ = (!lean_is_exclusive(v_x_545_)) as u8;
                    if v_isSharedCheck_559_ == 0 {
                        v___x_550_ = v_x_545_;
                        v_isShared_551_ = v_isSharedCheck_559_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_548_);
                        lean_dec(v_x_545_);
                        v___x_550_ = lean_box(0);
                        v_isShared_551_ = v_isSharedCheck_559_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_552_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___closed__3;
                v___x_553_ = l_Nat_reprFast(v_val_548_);
                if v_isShared_551_ == 0 {
                    lean_ctor_set_tag(v___x_550_, 3);
                    lean_ctor_set(v___x_550_, 0, v___x_553_);
                    v___x_555_ = v___x_550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_553_);
                    v___x_555_ = v_reuseFailAlloc_558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_556_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_556_, 0, v___x_552_);
                lean_ctor_set(v___x_556_, 1, v___x_555_);
                v___x_557_ = l_Repr_addAppParen(v___x_556_, v_x_546_);
                return v___x_557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0___boxed(
    mut v_x_560_: *mut LeanObject,
    mut v_x_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_562_: *mut LeanObject = core::ptr::null_mut();
    v_res_562_ =
        l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(v_x_560_, v_x_561_);
    lean_dec(v_x_561_);
    return v_res_562_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13() -> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_584_ = lean_unsigned_to_nat(2);
    v___x_585_ = lean_nat_to_int(v___x_584_);
    return v___x_585_;
}
pub unsafe fn _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14() -> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    v___x_586_ = lean_unsigned_to_nat(1);
    v___x_587_ = lean_nat_to_int(v___x_586_);
    return v___x_587_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent_repr(
    mut v_dir_600_: u8,
    mut v_x_601_: *mut LeanObject,
    mut v_prec_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: u8 = 0;
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: u8 = 0;
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358__overap_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: u8 = 0;
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: u8 = 0;
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_err_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: u8 = 0;
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: u8 = 0;
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_601_) {
                0 => {
                    v_head_638_ = lean_ctor_get(v_x_601_, 0);
                    lean_inc(v_head_638_);
                    lean_dec_ref_known(v_x_601_, 1);
                    v___x_650_ = lean_unsigned_to_nat(1024);
                    v___x_651_ = lean_nat_dec_le(v___x_650_, v_prec_602_);
                    if v___x_651_ == 0 {
                        v___x_652_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_640_ = v___x_652_;
                        state = 6;
                        continue;
                    } else {
                        v___x_653_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_640_ = v___x_653_;
                        state = 6;
                        continue;
                    }
                }
                1 => {
                    v_size_654_ = lean_ctor_get(v_x_601_, 0);
                    lean_inc(v_size_654_);
                    lean_dec_ref_known(v_x_601_, 1);
                    v___x_665_ = lean_unsigned_to_nat(1024);
                    v___x_666_ = lean_nat_dec_le(v___x_665_, v_prec_602_);
                    if v___x_666_ == 0 {
                        v___x_667_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_656_ = v___x_667_;
                        state = 7;
                        continue;
                    } else {
                        v___x_668_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_656_ = v___x_668_;
                        state = 7;
                        continue;
                    }
                }
                2 => {
                    v_err_669_ = lean_ctor_get(v_x_601_, 0);
                    lean_inc(v_err_669_);
                    lean_dec_ref_known(v_x_601_, 1);
                    v___x_680_ = lean_unsigned_to_nat(1024);
                    v___x_681_ = lean_nat_dec_le(v___x_680_, v_prec_602_);
                    if v___x_681_ == 0 {
                        v___x_682_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_671_ = v___x_682_;
                        state = 8;
                        continue;
                    } else {
                        v___x_683_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_671_ = v___x_683_;
                        state = 8;
                        continue;
                    }
                }
                3 => {
                    v___x_684_ = lean_unsigned_to_nat(1024);
                    v___x_685_ = lean_nat_dec_le(v___x_684_, v_prec_602_);
                    if v___x_685_ == 0 {
                        v___x_686_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_604_ = v___x_686_;
                        state = 1;
                        continue;
                    } else {
                        v___x_687_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_604_ = v___x_687_;
                        state = 1;
                        continue;
                    }
                }
                4 => {
                    v___x_688_ = lean_unsigned_to_nat(1024);
                    v___x_689_ = lean_nat_dec_le(v___x_688_, v_prec_602_);
                    if v___x_689_ == 0 {
                        v___x_690_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_611_ = v___x_690_;
                        state = 2;
                        continue;
                    } else {
                        v___x_691_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_611_ = v___x_691_;
                        state = 2;
                        continue;
                    }
                }
                5 => {
                    v___x_692_ = lean_unsigned_to_nat(1024);
                    v___x_693_ = lean_nat_dec_le(v___x_692_, v_prec_602_);
                    if v___x_693_ == 0 {
                        v___x_694_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_618_ = v___x_694_;
                        state = 3;
                        continue;
                    } else {
                        v___x_695_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_618_ = v___x_695_;
                        state = 3;
                        continue;
                    }
                }
                6 => {
                    v___x_696_ = lean_unsigned_to_nat(1024);
                    v___x_697_ = lean_nat_dec_le(v___x_696_, v_prec_602_);
                    if v___x_697_ == 0 {
                        v___x_698_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_625_ = v___x_698_;
                        state = 4;
                        continue;
                    } else {
                        v___x_699_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_625_ = v___x_699_;
                        state = 4;
                        continue;
                    }
                }
                _ => {
                    v___x_700_ = lean_unsigned_to_nat(1024);
                    v___x_701_ = lean_nat_dec_le(v___x_700_, v_prec_602_);
                    if v___x_701_ == 0 {
                        v___x_702_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__13,
                        );
                        v___y_632_ = v___x_702_;
                        state = 5;
                        continue;
                    } else {
                        v___x_703_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14_once
                            ),
                            _init_l_Std_Http_Protocol_H1_instReprEvent_repr___closed__14,
                        );
                        v___y_632_ = v___x_703_;
                        state = 5;
                        continue;
                    }
                }
            },
            1 => {
                v___x_605_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__1;
                lean_inc(v___y_604_);
                v___x_606_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_606_, 0, v___y_604_);
                lean_ctor_set(v___x_606_, 1, v___x_605_);
                v___x_607_ = 0;
                v___x_608_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_608_, 0, v___x_606_);
                lean_ctor_set_uint8(
                    v___x_608_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_607_,
                );
                v___x_609_ = l_Repr_addAppParen(v___x_608_, v_prec_602_);
                return v___x_609_;
            }
            2 => {
                v___x_612_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__3;
                lean_inc(v___y_611_);
                v___x_613_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_613_, 0, v___y_611_);
                lean_ctor_set(v___x_613_, 1, v___x_612_);
                v___x_614_ = 0;
                v___x_615_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_615_, 0, v___x_613_);
                lean_ctor_set_uint8(
                    v___x_615_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_614_,
                );
                v___x_616_ = l_Repr_addAppParen(v___x_615_, v_prec_602_);
                return v___x_616_;
            }
            3 => {
                v___x_619_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__5;
                lean_inc(v___y_618_);
                v___x_620_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_620_, 0, v___y_618_);
                lean_ctor_set(v___x_620_, 1, v___x_619_);
                v___x_621_ = 0;
                v___x_622_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_622_, 0, v___x_620_);
                lean_ctor_set_uint8(
                    v___x_622_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_621_,
                );
                v___x_623_ = l_Repr_addAppParen(v___x_622_, v_prec_602_);
                return v___x_623_;
            }
            4 => {
                v___x_626_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__7;
                lean_inc(v___y_625_);
                v___x_627_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_627_, 0, v___y_625_);
                lean_ctor_set(v___x_627_, 1, v___x_626_);
                v___x_628_ = 0;
                v___x_629_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_629_, 0, v___x_627_);
                lean_ctor_set_uint8(
                    v___x_629_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_628_,
                );
                v___x_630_ = l_Repr_addAppParen(v___x_629_, v_prec_602_);
                return v___x_630_;
            }
            5 => {
                v___x_633_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__9;
                lean_inc(v___y_632_);
                v___x_634_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_634_, 0, v___y_632_);
                lean_ctor_set(v___x_634_, 1, v___x_633_);
                v___x_635_ = 0;
                v___x_636_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_636_, 0, v___x_634_);
                lean_ctor_set_uint8(
                    v___x_636_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_635_,
                );
                v___x_637_ = l_Repr_addAppParen(v___x_636_, v_prec_602_);
                return v___x_637_;
            }
            6 => {
                v___x_641_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__12;
                v___x_642_ = lean_unsigned_to_nat(1024);
                v___x_358__overap_643_ = l_Std_Http_Protocol_H1_instReprHead(v_dir_600_);
                v___x_644_ = lean_apply_2(v___x_358__overap_643_, v_head_638_, v___x_642_);
                v___x_645_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_645_, 0, v___x_641_);
                lean_ctor_set(v___x_645_, 1, v___x_644_);
                lean_inc(v___y_640_);
                v___x_646_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_646_, 0, v___y_640_);
                lean_ctor_set(v___x_646_, 1, v___x_645_);
                v___x_647_ = 0;
                v___x_648_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_648_, 0, v___x_646_);
                lean_ctor_set_uint8(
                    v___x_648_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_647_,
                );
                v___x_649_ = l_Repr_addAppParen(v___x_648_, v_prec_602_);
                return v___x_649_;
            }
            7 => {
                v___x_657_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__17;
                v___x_658_ = lean_unsigned_to_nat(1024);
                v___x_659_ = l_Option_repr___at___00Std_Http_Protocol_H1_instReprEvent_repr_spec__0(
                    v_size_654_,
                    v___x_658_,
                );
                v___x_660_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_660_, 0, v___x_657_);
                lean_ctor_set(v___x_660_, 1, v___x_659_);
                lean_inc(v___y_656_);
                v___x_661_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_661_, 0, v___y_656_);
                lean_ctor_set(v___x_661_, 1, v___x_660_);
                v___x_662_ = 0;
                v___x_663_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_663_, 0, v___x_661_);
                lean_ctor_set_uint8(
                    v___x_663_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_662_,
                );
                v___x_664_ = l_Repr_addAppParen(v___x_663_, v_prec_602_);
                return v___x_664_;
            }
            8 => {
                v___x_672_ = l_Std_Http_Protocol_H1_instReprEvent_repr___closed__20;
                v___x_673_ = lean_unsigned_to_nat(1024);
                v___x_674_ = l_Std_Http_Protocol_H1_instReprError_repr(v_err_669_, v___x_673_);
                v___x_675_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_675_, 0, v___x_672_);
                lean_ctor_set(v___x_675_, 1, v___x_674_);
                lean_inc(v___y_671_);
                v___x_676_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_676_, 0, v___y_671_);
                lean_ctor_set(v___x_676_, 1, v___x_675_);
                v___x_677_ = 0;
                v___x_678_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_678_, 0, v___x_676_);
                lean_ctor_set_uint8(
                    v___x_678_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_677_,
                );
                v___x_679_ = l_Repr_addAppParen(v___x_678_, v_prec_602_);
                return v___x_679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent_repr___boxed(
    mut v_dir_704_: *mut LeanObject,
    mut v_x_705_: *mut LeanObject,
    mut v_prec_706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_701__boxed_707_: u8 = 0;
    let mut v_res_708_: *mut LeanObject = core::ptr::null_mut();
    v_dir_701__boxed_707_ = (lean_unbox(v_dir_704_) as u8);
    v_res_708_ =
        l_Std_Http_Protocol_H1_instReprEvent_repr(v_dir_701__boxed_707_, v_x_705_, v_prec_706_);
    lean_dec(v_prec_706_);
    return v_res_708_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent(mut v_dir_709_: u8) -> *mut LeanObject {
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    v___x_710_ = lean_box((v_dir_709_) as usize);
    v___x_711_ = lean_alloc_closure(
        l_Std_Http_Protocol_H1_instReprEvent_repr___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_711_, 0, v___x_710_);
    return v___x_711_;
}
pub unsafe fn l_Std_Http_Protocol_H1_instReprEvent___boxed(
    mut v_dir_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dir_5__boxed_713_: u8 = 0;
    let mut v_res_714_: *mut LeanObject = core::ptr::null_mut();
    v_dir_5__boxed_713_ = (lean_unbox(v_dir_712_) as u8);
    v_res_714_ = l_Std_Http_Protocol_H1_instReprEvent(v_dir_5__boxed_713_);
    return v_res_714_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Protocol_H1_Event(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Protocol_H1_Event(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Protocol_H1_Event(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Internal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Protocol_H1_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Protocol_H1_Event(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Protocol_H1_Event(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Protocol_H1_Event(builtin);
}
