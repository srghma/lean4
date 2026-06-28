// Lean compiler output
// Module: Std.Internal.UV.System
// Imports: Init.System.Promise Init.Data.SInt Std.Net
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::SInt::{
    initialize_Init_Data_SInt, runtime_initialize_Init_Data_SInt,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Std::Net::{initialize_Std_Net, runtime_initialize_Std_Net};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_to_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
    lean_uint64_of_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0_value:
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
    m_data: [123, 32, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [117, 115, 101, 114, 84, 105, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__2_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 32, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__3_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 121, 115, 116, 101, 109, 84, 105, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13_value:
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
    m_data: [109, 97, 120, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__13_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16_value:
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
    m_data: [105, 120, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__16_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19_value:
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
    m_data: [105, 100, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__19_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21_value:
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
    m_data: [105, 115, 82, 83, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__21_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23_value:
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
    m_data: [109, 105, 110, 70, 108, 116, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__23_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25_value:
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
    m_data: [109, 97, 106, 70, 108, 116, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__25_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27_value:
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
    m_data: [110, 83, 119, 97, 112, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__27_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [105, 110, 66, 108, 111, 99, 107, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__29_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 117, 116, 66, 108, 111, 99, 107, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__32_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 115, 103, 83, 101, 110, 116, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__34_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 115, 103, 82, 101, 99, 118, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__36_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 105, 103, 110, 97, 108, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__38_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [118, 111, 108, 117, 110, 116, 97, 114, 121, 67, 83, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__40_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        105, 110, 118, 111, 108, 117, 110, 116, 97, 114, 121, 67, 83, 0,
    ],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__43_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46_value:
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
    m_data: [32, 125, 0],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__46_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprRUsage___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_UV_System_instReprRUsage_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_UV_System_instReprRUsage___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instReprRUsage: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0: u64 = 0;
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedRUsage_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedRUsage: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [117, 115, 101, 114, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 105, 99, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 121, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__7_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [105, 100, 108, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [105, 114, 113, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__12_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUTimes___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_UV_System_instReprCPUTimes_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_UV_System_instReprCPUTimes___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instReprCPUTimes: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUTimes___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUTimes_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUTimes: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0_value:
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
    m_data: [109, 111, 100, 101, 108, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4_value:
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
    m_data: [115, 112, 101, 101, 100, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6_value:
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
    m_data: [116, 105, 109, 101, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__6_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprCPUInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_UV_System_instReprCPUInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_UV_System_instReprCPUInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instReprCPUInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprCPUInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value:
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
static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedCPUInfo: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 111, 110, 101, 0]};
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 111, 109, 101, 32, 0]};
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2_value) as *mut LeanObject;
pub static l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__2_value) as *mut LeanObject] };
static mut l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3_value) as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [117, 115, 101, 114, 110, 97, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [117, 105, 100, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [103, 105, 100, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__6_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8_value:
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
    m_data: [115, 104, 101, 108, 108, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [104, 111, 109, 101, 100, 105, 114, 0],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10_value
)
    as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__10_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11: *mut LeanObject = core::ptr::addr_of!(
    l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11_value
)
    as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprPasswdInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_UV_System_instReprPasswdInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_UV_System_instReprPasswdInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instReprPasswdInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprPasswdInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value:
    LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedPasswdInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedPasswdInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedPasswdInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5_value) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__2_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6_value) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7_value) as *mut LeanObject;
pub static l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__7_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8_value) as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [103, 114, 111, 117, 112, 110, 97, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 101, 109, 98, 101, 114, 115, 0],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__5_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprGroupInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_UV_System_instReprGroupInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_UV_System_instReprGroupInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instReprGroupInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprGroupInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedGroupInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Internal_UV_System_instInhabitedGroupInfo: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 121, 115, 110, 97, 109, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__2_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 108, 101, 97, 115, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__4_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 101, 114, 115, 105, 111, 110, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__6_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 97, 99, 104, 105, 110, 101, 0],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__8_value
    ) as *mut LeanObject],
};
static mut l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instReprUnameInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Internal_UV_System_instReprUnameInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Internal_UV_System_instReprUnameInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instReprUnameInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instReprUnameInfo___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value:
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
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedUnameInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Internal_UV_System_instInhabitedUnameInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Internal_UV_System_instInhabitedUnameInfo_default___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Internal_UV_System_instReprRUsage_repr_spec__0(
    mut v_a_976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v___x_977_ = lean_nat_to_int(v_a_976_);
    return v___x_977_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    v___x_991_ = lean_unsigned_to_nat(12);
    v___x_992_ = lean_nat_to_int(v___x_991_);
    return v___x_992_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12()
-> *mut LeanObject {
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    v___x_999_ = lean_unsigned_to_nat(14);
    v___x_1000_ = lean_nat_to_int(v___x_999_);
    return v___x_1000_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_1004_ = lean_unsigned_to_nat(10);
    v___x_1005_ = lean_nat_to_int(v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18()
-> *mut LeanObject {
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    v___x_1009_ = lean_unsigned_to_nat(9);
    v___x_1010_ = lean_nat_to_int(v___x_1009_);
    return v___x_1010_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31()
-> *mut LeanObject {
    let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    v___x_1029_ = lean_unsigned_to_nat(11);
    v___x_1030_ = lean_nat_to_int(v___x_1029_);
    return v___x_1030_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42()
-> *mut LeanObject {
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    v___x_1046_ = lean_unsigned_to_nat(15);
    v___x_1047_ = lean_nat_to_int(v___x_1046_);
    return v___x_1047_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45()
-> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ = lean_unsigned_to_nat(17);
    v___x_1052_ = lean_nat_to_int(v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47()
-> *mut LeanObject {
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__0;
    v___x_1055_ = lean_string_length(v___x_1054_);
    return v___x_1055_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48()
-> *mut LeanObject {
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1056_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__47,
    );
    v___x_1057_ = lean_nat_to_int(v___x_1056_);
    return v___x_1057_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr___redArg(
    mut v_x_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_userTime_1063_: u64 = 0;
    let mut v_systemTime_1064_: u64 = 0;
    let mut v_maxRSS_1065_: u64 = 0;
    let mut v_ixRSS_1066_: u64 = 0;
    let mut v_idRSS_1067_: u64 = 0;
    let mut v_isRSS_1068_: u64 = 0;
    let mut v_minFlt_1069_: u64 = 0;
    let mut v_majFlt_1070_: u64 = 0;
    let mut v_nSwap_1071_: u64 = 0;
    let mut v_inBlock_1072_: u64 = 0;
    let mut v_outBlock_1073_: u64 = 0;
    let mut v_msgSent_1074_: u64 = 0;
    let mut v_msgRecv_1075_: u64 = 0;
    let mut v_signals_1076_: u64 = 0;
    let mut v_voluntaryCS_1077_: u64 = 0;
    let mut v_involuntaryCS_1078_: u64 = 0;
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    v_userTime_1063_ = lean_ctor_get_uint64(v_x_1062_, 0 as u32);
    v_systemTime_1064_ = lean_ctor_get_uint64(v_x_1062_, 8 as u32);
    v_maxRSS_1065_ = lean_ctor_get_uint64(v_x_1062_, 16 as u32);
    v_ixRSS_1066_ = lean_ctor_get_uint64(v_x_1062_, 24 as u32);
    v_idRSS_1067_ = lean_ctor_get_uint64(v_x_1062_, 32 as u32);
    v_isRSS_1068_ = lean_ctor_get_uint64(v_x_1062_, 40 as u32);
    v_minFlt_1069_ = lean_ctor_get_uint64(v_x_1062_, 48 as u32);
    v_majFlt_1070_ = lean_ctor_get_uint64(v_x_1062_, 56 as u32);
    v_nSwap_1071_ = lean_ctor_get_uint64(v_x_1062_, 64 as u32);
    v_inBlock_1072_ = lean_ctor_get_uint64(v_x_1062_, 72 as u32);
    v_outBlock_1073_ = lean_ctor_get_uint64(v_x_1062_, 80 as u32);
    v_msgSent_1074_ = lean_ctor_get_uint64(v_x_1062_, 88 as u32);
    v_msgRecv_1075_ = lean_ctor_get_uint64(v_x_1062_, 96 as u32);
    v_signals_1076_ = lean_ctor_get_uint64(v_x_1062_, 104 as u32);
    v_voluntaryCS_1077_ = lean_ctor_get_uint64(v_x_1062_, 112 as u32);
    v_involuntaryCS_1078_ = lean_ctor_get_uint64(v_x_1062_, 120 as u32);
    v___x_1079_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1080_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__6;
    v___x_1081_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7,
    );
    v___x_1082_ = lean_uint64_to_nat(v_userTime_1063_);
    v___x_1083_ = l_Nat_reprFast(v___x_1082_);
    v___x_1084_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1084_, 0, v___x_1083_);
    v___x_1085_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1085_, 0, v___x_1081_);
    lean_ctor_set(v___x_1085_, 1, v___x_1084_);
    v___x_1086_ = 0;
    v___x_1087_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1087_, 0, v___x_1085_);
    lean_ctor_set_uint8(
        v___x_1087_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1088_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1088_, 0, v___x_1080_);
    lean_ctor_set(v___x_1088_, 1, v___x_1087_);
    v___x_1089_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1090_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1090_, 0, v___x_1088_);
    lean_ctor_set(v___x_1090_, 1, v___x_1089_);
    v___x_1091_ = lean_box(1);
    v___x_1092_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1092_, 0, v___x_1090_);
    lean_ctor_set(v___x_1092_, 1, v___x_1091_);
    v___x_1093_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__11;
    v___x_1094_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1094_, 0, v___x_1092_);
    lean_ctor_set(v___x_1094_, 1, v___x_1093_);
    v___x_1095_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    lean_ctor_set(v___x_1095_, 1, v___x_1079_);
    v___x_1096_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__12,
    );
    v___x_1097_ = lean_uint64_to_nat(v_systemTime_1064_);
    v___x_1098_ = l_Nat_reprFast(v___x_1097_);
    v___x_1099_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1099_, 0, v___x_1098_);
    v___x_1100_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1100_, 0, v___x_1096_);
    lean_ctor_set(v___x_1100_, 1, v___x_1099_);
    v___x_1101_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1101_, 0, v___x_1100_);
    lean_ctor_set_uint8(
        v___x_1101_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1102_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1102_, 0, v___x_1095_);
    lean_ctor_set(v___x_1102_, 1, v___x_1101_);
    v___x_1103_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1103_, 0, v___x_1102_);
    lean_ctor_set(v___x_1103_, 1, v___x_1089_);
    v___x_1104_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1104_, 0, v___x_1103_);
    lean_ctor_set(v___x_1104_, 1, v___x_1091_);
    v___x_1105_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__14;
    v___x_1106_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1106_, 0, v___x_1104_);
    lean_ctor_set(v___x_1106_, 1, v___x_1105_);
    v___x_1107_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1107_, 0, v___x_1106_);
    lean_ctor_set(v___x_1107_, 1, v___x_1079_);
    v___x_1108_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__15,
    );
    v___x_1109_ = lean_uint64_to_nat(v_maxRSS_1065_);
    v___x_1110_ = l_Nat_reprFast(v___x_1109_);
    v___x_1111_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1111_, 0, v___x_1110_);
    v___x_1112_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1112_, 0, v___x_1108_);
    lean_ctor_set(v___x_1112_, 1, v___x_1111_);
    v___x_1113_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1113_, 0, v___x_1112_);
    lean_ctor_set_uint8(
        v___x_1113_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1114_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1114_, 0, v___x_1107_);
    lean_ctor_set(v___x_1114_, 1, v___x_1113_);
    v___x_1115_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1115_, 0, v___x_1114_);
    lean_ctor_set(v___x_1115_, 1, v___x_1089_);
    v___x_1116_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1116_, 0, v___x_1115_);
    lean_ctor_set(v___x_1116_, 1, v___x_1091_);
    v___x_1117_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__17;
    v___x_1118_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1118_, 0, v___x_1116_);
    lean_ctor_set(v___x_1118_, 1, v___x_1117_);
    v___x_1119_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1119_, 0, v___x_1118_);
    lean_ctor_set(v___x_1119_, 1, v___x_1079_);
    v___x_1120_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18,
    );
    v___x_1121_ = lean_uint64_to_nat(v_ixRSS_1066_);
    v___x_1122_ = l_Nat_reprFast(v___x_1121_);
    v___x_1123_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1123_, 0, v___x_1122_);
    v___x_1124_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1124_, 0, v___x_1120_);
    lean_ctor_set(v___x_1124_, 1, v___x_1123_);
    v___x_1125_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1125_, 0, v___x_1124_);
    lean_ctor_set_uint8(
        v___x_1125_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1126_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1126_, 0, v___x_1119_);
    lean_ctor_set(v___x_1126_, 1, v___x_1125_);
    v___x_1127_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    lean_ctor_set(v___x_1127_, 1, v___x_1089_);
    v___x_1128_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1128_, 0, v___x_1127_);
    lean_ctor_set(v___x_1128_, 1, v___x_1091_);
    v___x_1129_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__20;
    v___x_1130_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1130_, 0, v___x_1128_);
    lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    v___x_1131_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1131_, 0, v___x_1130_);
    lean_ctor_set(v___x_1131_, 1, v___x_1079_);
    v___x_1132_ = lean_uint64_to_nat(v_idRSS_1067_);
    v___x_1133_ = l_Nat_reprFast(v___x_1132_);
    v___x_1134_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1134_, 0, v___x_1133_);
    v___x_1135_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1135_, 0, v___x_1120_);
    lean_ctor_set(v___x_1135_, 1, v___x_1134_);
    v___x_1136_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1136_, 0, v___x_1135_);
    lean_ctor_set_uint8(
        v___x_1136_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1137_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1137_, 0, v___x_1131_);
    lean_ctor_set(v___x_1137_, 1, v___x_1136_);
    v___x_1138_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1138_, 0, v___x_1137_);
    lean_ctor_set(v___x_1138_, 1, v___x_1089_);
    v___x_1139_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    lean_ctor_set(v___x_1139_, 1, v___x_1091_);
    v___x_1140_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__22;
    v___x_1141_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1141_, 0, v___x_1139_);
    lean_ctor_set(v___x_1141_, 1, v___x_1140_);
    v___x_1142_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1142_, 0, v___x_1141_);
    lean_ctor_set(v___x_1142_, 1, v___x_1079_);
    v___x_1143_ = lean_uint64_to_nat(v_isRSS_1068_);
    v___x_1144_ = l_Nat_reprFast(v___x_1143_);
    v___x_1145_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1145_, 0, v___x_1144_);
    v___x_1146_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1146_, 0, v___x_1120_);
    lean_ctor_set(v___x_1146_, 1, v___x_1145_);
    v___x_1147_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1147_, 0, v___x_1146_);
    lean_ctor_set_uint8(
        v___x_1147_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1148_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1148_, 0, v___x_1142_);
    lean_ctor_set(v___x_1148_, 1, v___x_1147_);
    v___x_1149_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1149_, 0, v___x_1148_);
    lean_ctor_set(v___x_1149_, 1, v___x_1089_);
    v___x_1150_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1150_, 0, v___x_1149_);
    lean_ctor_set(v___x_1150_, 1, v___x_1091_);
    v___x_1151_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__24;
    v___x_1152_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1152_, 0, v___x_1150_);
    lean_ctor_set(v___x_1152_, 1, v___x_1151_);
    v___x_1153_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1153_, 0, v___x_1152_);
    lean_ctor_set(v___x_1153_, 1, v___x_1079_);
    v___x_1154_ = lean_uint64_to_nat(v_minFlt_1069_);
    v___x_1155_ = l_Nat_reprFast(v___x_1154_);
    v___x_1156_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1156_, 0, v___x_1155_);
    v___x_1157_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1157_, 0, v___x_1108_);
    lean_ctor_set(v___x_1157_, 1, v___x_1156_);
    v___x_1158_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1158_, 0, v___x_1157_);
    lean_ctor_set_uint8(
        v___x_1158_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1159_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1159_, 0, v___x_1153_);
    lean_ctor_set(v___x_1159_, 1, v___x_1158_);
    v___x_1160_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1160_, 0, v___x_1159_);
    lean_ctor_set(v___x_1160_, 1, v___x_1089_);
    v___x_1161_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1161_, 0, v___x_1160_);
    lean_ctor_set(v___x_1161_, 1, v___x_1091_);
    v___x_1162_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__26;
    v___x_1163_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1163_, 0, v___x_1161_);
    lean_ctor_set(v___x_1163_, 1, v___x_1162_);
    v___x_1164_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1164_, 0, v___x_1163_);
    lean_ctor_set(v___x_1164_, 1, v___x_1079_);
    v___x_1165_ = lean_uint64_to_nat(v_majFlt_1070_);
    v___x_1166_ = l_Nat_reprFast(v___x_1165_);
    v___x_1167_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1167_, 0, v___x_1166_);
    v___x_1168_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1168_, 0, v___x_1108_);
    lean_ctor_set(v___x_1168_, 1, v___x_1167_);
    v___x_1169_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1169_, 0, v___x_1168_);
    lean_ctor_set_uint8(
        v___x_1169_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1170_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1170_, 0, v___x_1164_);
    lean_ctor_set(v___x_1170_, 1, v___x_1169_);
    v___x_1171_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1171_, 0, v___x_1170_);
    lean_ctor_set(v___x_1171_, 1, v___x_1089_);
    v___x_1172_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1172_, 0, v___x_1171_);
    lean_ctor_set(v___x_1172_, 1, v___x_1091_);
    v___x_1173_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__28;
    v___x_1174_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1174_, 0, v___x_1172_);
    lean_ctor_set(v___x_1174_, 1, v___x_1173_);
    v___x_1175_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1175_, 0, v___x_1174_);
    lean_ctor_set(v___x_1175_, 1, v___x_1079_);
    v___x_1176_ = lean_uint64_to_nat(v_nSwap_1071_);
    v___x_1177_ = l_Nat_reprFast(v___x_1176_);
    v___x_1178_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1178_, 0, v___x_1177_);
    v___x_1179_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1179_, 0, v___x_1120_);
    lean_ctor_set(v___x_1179_, 1, v___x_1178_);
    v___x_1180_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1180_, 0, v___x_1179_);
    lean_ctor_set_uint8(
        v___x_1180_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1181_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1181_, 0, v___x_1175_);
    lean_ctor_set(v___x_1181_, 1, v___x_1180_);
    v___x_1182_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1182_, 0, v___x_1181_);
    lean_ctor_set(v___x_1182_, 1, v___x_1089_);
    v___x_1183_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1183_, 0, v___x_1182_);
    lean_ctor_set(v___x_1183_, 1, v___x_1091_);
    v___x_1184_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__30;
    v___x_1185_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1185_, 0, v___x_1183_);
    lean_ctor_set(v___x_1185_, 1, v___x_1184_);
    v___x_1186_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1186_, 0, v___x_1185_);
    lean_ctor_set(v___x_1186_, 1, v___x_1079_);
    v___x_1187_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1188_ = lean_uint64_to_nat(v_inBlock_1072_);
    v___x_1189_ = l_Nat_reprFast(v___x_1188_);
    v___x_1190_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1190_, 0, v___x_1189_);
    v___x_1191_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1191_, 0, v___x_1187_);
    lean_ctor_set(v___x_1191_, 1, v___x_1190_);
    v___x_1192_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1192_, 0, v___x_1191_);
    lean_ctor_set_uint8(
        v___x_1192_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1193_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1193_, 0, v___x_1186_);
    lean_ctor_set(v___x_1193_, 1, v___x_1192_);
    v___x_1194_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1194_, 0, v___x_1193_);
    lean_ctor_set(v___x_1194_, 1, v___x_1089_);
    v___x_1195_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1195_, 0, v___x_1194_);
    lean_ctor_set(v___x_1195_, 1, v___x_1091_);
    v___x_1196_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__33;
    v___x_1197_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1197_, 0, v___x_1195_);
    lean_ctor_set(v___x_1197_, 1, v___x_1196_);
    v___x_1198_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1198_, 0, v___x_1197_);
    lean_ctor_set(v___x_1198_, 1, v___x_1079_);
    v___x_1199_ = lean_uint64_to_nat(v_outBlock_1073_);
    v___x_1200_ = l_Nat_reprFast(v___x_1199_);
    v___x_1201_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1201_, 0, v___x_1200_);
    v___x_1202_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1202_, 0, v___x_1081_);
    lean_ctor_set(v___x_1202_, 1, v___x_1201_);
    v___x_1203_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1203_, 0, v___x_1202_);
    lean_ctor_set_uint8(
        v___x_1203_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1204_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1204_, 0, v___x_1198_);
    lean_ctor_set(v___x_1204_, 1, v___x_1203_);
    v___x_1205_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1205_, 0, v___x_1204_);
    lean_ctor_set(v___x_1205_, 1, v___x_1089_);
    v___x_1206_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1206_, 0, v___x_1205_);
    lean_ctor_set(v___x_1206_, 1, v___x_1091_);
    v___x_1207_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__35;
    v___x_1208_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1208_, 0, v___x_1206_);
    lean_ctor_set(v___x_1208_, 1, v___x_1207_);
    v___x_1209_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1209_, 0, v___x_1208_);
    lean_ctor_set(v___x_1209_, 1, v___x_1079_);
    v___x_1210_ = lean_uint64_to_nat(v_msgSent_1074_);
    v___x_1211_ = l_Nat_reprFast(v___x_1210_);
    v___x_1212_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1212_, 0, v___x_1211_);
    v___x_1213_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1213_, 0, v___x_1187_);
    lean_ctor_set(v___x_1213_, 1, v___x_1212_);
    v___x_1214_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1214_, 0, v___x_1213_);
    lean_ctor_set_uint8(
        v___x_1214_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1215_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1215_, 0, v___x_1209_);
    lean_ctor_set(v___x_1215_, 1, v___x_1214_);
    v___x_1216_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1216_, 0, v___x_1215_);
    lean_ctor_set(v___x_1216_, 1, v___x_1089_);
    v___x_1217_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1217_, 0, v___x_1216_);
    lean_ctor_set(v___x_1217_, 1, v___x_1091_);
    v___x_1218_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__37;
    v___x_1219_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1219_, 0, v___x_1217_);
    lean_ctor_set(v___x_1219_, 1, v___x_1218_);
    v___x_1220_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1220_, 0, v___x_1219_);
    lean_ctor_set(v___x_1220_, 1, v___x_1079_);
    v___x_1221_ = lean_uint64_to_nat(v_msgRecv_1075_);
    v___x_1222_ = l_Nat_reprFast(v___x_1221_);
    v___x_1223_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1223_, 0, v___x_1222_);
    v___x_1224_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1224_, 0, v___x_1187_);
    lean_ctor_set(v___x_1224_, 1, v___x_1223_);
    v___x_1225_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1225_, 0, v___x_1224_);
    lean_ctor_set_uint8(
        v___x_1225_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1226_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1226_, 0, v___x_1220_);
    lean_ctor_set(v___x_1226_, 1, v___x_1225_);
    v___x_1227_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1227_, 0, v___x_1226_);
    lean_ctor_set(v___x_1227_, 1, v___x_1089_);
    v___x_1228_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1228_, 0, v___x_1227_);
    lean_ctor_set(v___x_1228_, 1, v___x_1091_);
    v___x_1229_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__39;
    v___x_1230_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1230_, 0, v___x_1228_);
    lean_ctor_set(v___x_1230_, 1, v___x_1229_);
    v___x_1231_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1231_, 0, v___x_1230_);
    lean_ctor_set(v___x_1231_, 1, v___x_1079_);
    v___x_1232_ = lean_uint64_to_nat(v_signals_1076_);
    v___x_1233_ = l_Nat_reprFast(v___x_1232_);
    v___x_1234_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1234_, 0, v___x_1233_);
    v___x_1235_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1235_, 0, v___x_1187_);
    lean_ctor_set(v___x_1235_, 1, v___x_1234_);
    v___x_1236_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1236_, 0, v___x_1235_);
    lean_ctor_set_uint8(
        v___x_1236_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1237_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1237_, 0, v___x_1231_);
    lean_ctor_set(v___x_1237_, 1, v___x_1236_);
    v___x_1238_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    lean_ctor_set(v___x_1238_, 1, v___x_1089_);
    v___x_1239_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1239_, 0, v___x_1238_);
    lean_ctor_set(v___x_1239_, 1, v___x_1091_);
    v___x_1240_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__41;
    v___x_1241_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1241_, 0, v___x_1239_);
    lean_ctor_set(v___x_1241_, 1, v___x_1240_);
    v___x_1242_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1242_, 0, v___x_1241_);
    lean_ctor_set(v___x_1242_, 1, v___x_1079_);
    v___x_1243_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__42,
    );
    v___x_1244_ = lean_uint64_to_nat(v_voluntaryCS_1077_);
    v___x_1245_ = l_Nat_reprFast(v___x_1244_);
    v___x_1246_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1246_, 0, v___x_1245_);
    v___x_1247_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1247_, 0, v___x_1243_);
    lean_ctor_set(v___x_1247_, 1, v___x_1246_);
    v___x_1248_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1248_, 0, v___x_1247_);
    lean_ctor_set_uint8(
        v___x_1248_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1249_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1249_, 0, v___x_1242_);
    lean_ctor_set(v___x_1249_, 1, v___x_1248_);
    v___x_1250_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1250_, 0, v___x_1249_);
    lean_ctor_set(v___x_1250_, 1, v___x_1089_);
    v___x_1251_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1251_, 0, v___x_1250_);
    lean_ctor_set(v___x_1251_, 1, v___x_1091_);
    v___x_1252_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__44;
    v___x_1253_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1253_, 0, v___x_1251_);
    lean_ctor_set(v___x_1253_, 1, v___x_1252_);
    v___x_1254_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1254_, 0, v___x_1253_);
    lean_ctor_set(v___x_1254_, 1, v___x_1079_);
    v___x_1255_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__45,
    );
    v___x_1256_ = lean_uint64_to_nat(v_involuntaryCS_1078_);
    v___x_1257_ = l_Nat_reprFast(v___x_1256_);
    v___x_1258_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1258_, 0, v___x_1257_);
    v___x_1259_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1259_, 0, v___x_1255_);
    lean_ctor_set(v___x_1259_, 1, v___x_1258_);
    v___x_1260_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1260_, 0, v___x_1259_);
    lean_ctor_set_uint8(
        v___x_1260_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    v___x_1261_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1261_, 0, v___x_1254_);
    lean_ctor_set(v___x_1261_, 1, v___x_1260_);
    v___x_1262_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1263_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1264_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1264_, 0, v___x_1263_);
    lean_ctor_set(v___x_1264_, 1, v___x_1261_);
    v___x_1265_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1266_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1266_, 0, v___x_1264_);
    lean_ctor_set(v___x_1266_, 1, v___x_1265_);
    v___x_1267_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1267_, 0, v___x_1262_);
    lean_ctor_set(v___x_1267_, 1, v___x_1266_);
    v___x_1268_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1268_, 0, v___x_1267_);
    lean_ctor_set_uint8(
        v___x_1268_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1086_,
    );
    return v___x_1268_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr___redArg___boxed(
    mut v_x_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg(v_x_1269_);
    lean_dec_ref(v_x_1269_);
    return v_res_1270_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr(
    mut v_x_1271_: *mut LeanObject,
    mut v_prec_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1273_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg(v_x_1271_);
    return v___x_1273_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprRUsage_repr___boxed(
    mut v_x_1274_: *mut LeanObject,
    mut v_prec_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1276_: *mut LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Std_Internal_UV_System_instReprRUsage_repr(v_x_1274_, v_prec_1275_);
    lean_dec(v_prec_1275_);
    lean_dec_ref(v_x_1274_);
    return v_res_1276_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0() -> u64 {
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: u64 = 0;
    v___x_1279_ = lean_unsigned_to_nat(0);
    v___x_1280_ = lean_uint64_of_nat(v___x_1279_);
    return v___x_1280_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1()
-> *mut LeanObject {
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1282_ = lean_alloc_ctor(0, 0, (128) as u32);
    lean_ctor_set_uint64(v___x_1282_, 0 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 8 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 16 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 24 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 32 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 40 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 48 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 56 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 64 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 72 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 80 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 88 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 96 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 104 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 112 as u32, v___x_1281_);
    lean_ctor_set_uint64(v___x_1282_, 120 as u32, v___x_1281_);
    return v___x_1282_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage_default() -> *mut LeanObject {
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    v___x_1283_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__1,
    );
    return v___x_1283_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedRUsage() -> *mut LeanObject {
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    v___x_1284_ = l_Std_Internal_UV_System_instInhabitedRUsage_default;
    return v___x_1284_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    v___x_1294_ = lean_unsigned_to_nat(8);
    v___x_1295_ = lean_nat_to_int(v___x_1294_);
    return v___x_1295_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = lean_unsigned_to_nat(7);
    v___x_1303_ = lean_nat_to_int(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(
    mut v_x_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_user_1311_: u64 = 0;
    let mut v_nice_1312_: u64 = 0;
    let mut v_sys_1313_: u64 = 0;
    let mut v_idle_1314_: u64 = 0;
    let mut v_irq_1315_: u64 = 0;
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    v_user_1311_ = lean_ctor_get_uint64(v_x_1310_, 0 as u32);
    v_nice_1312_ = lean_ctor_get_uint64(v_x_1310_, 8 as u32);
    v_sys_1313_ = lean_ctor_get_uint64(v_x_1310_, 16 as u32);
    v_idle_1314_ = lean_ctor_get_uint64(v_x_1310_, 24 as u32);
    v_irq_1315_ = lean_ctor_get_uint64(v_x_1310_, 32 as u32);
    v___x_1316_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1317_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__3;
    v___x_1318_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__4,
    );
    v___x_1319_ = lean_uint64_to_nat(v_user_1311_);
    v___x_1320_ = l_Nat_reprFast(v___x_1319_);
    v___x_1321_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1321_, 0, v___x_1320_);
    v___x_1322_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1322_, 0, v___x_1318_);
    lean_ctor_set(v___x_1322_, 1, v___x_1321_);
    v___x_1323_ = 0;
    v___x_1324_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1324_, 0, v___x_1322_);
    lean_ctor_set_uint8(
        v___x_1324_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1325_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1325_, 0, v___x_1317_);
    lean_ctor_set(v___x_1325_, 1, v___x_1324_);
    v___x_1326_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1327_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1327_, 0, v___x_1325_);
    lean_ctor_set(v___x_1327_, 1, v___x_1326_);
    v___x_1328_ = lean_box(1);
    v___x_1329_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1329_, 0, v___x_1327_);
    lean_ctor_set(v___x_1329_, 1, v___x_1328_);
    v___x_1330_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__6;
    v___x_1331_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1331_, 0, v___x_1329_);
    lean_ctor_set(v___x_1331_, 1, v___x_1330_);
    v___x_1332_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1332_, 0, v___x_1331_);
    lean_ctor_set(v___x_1332_, 1, v___x_1316_);
    v___x_1333_ = lean_uint64_to_nat(v_nice_1312_);
    v___x_1334_ = l_Nat_reprFast(v___x_1333_);
    v___x_1335_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1335_, 0, v___x_1334_);
    v___x_1336_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1336_, 0, v___x_1318_);
    lean_ctor_set(v___x_1336_, 1, v___x_1335_);
    v___x_1337_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1337_, 0, v___x_1336_);
    lean_ctor_set_uint8(
        v___x_1337_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1338_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1338_, 0, v___x_1332_);
    lean_ctor_set(v___x_1338_, 1, v___x_1337_);
    v___x_1339_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1339_, 0, v___x_1338_);
    lean_ctor_set(v___x_1339_, 1, v___x_1326_);
    v___x_1340_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1340_, 0, v___x_1339_);
    lean_ctor_set(v___x_1340_, 1, v___x_1328_);
    v___x_1341_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__8;
    v___x_1342_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1342_, 0, v___x_1340_);
    lean_ctor_set(v___x_1342_, 1, v___x_1341_);
    v___x_1343_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1343_, 0, v___x_1342_);
    lean_ctor_set(v___x_1343_, 1, v___x_1316_);
    v___x_1344_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9,
    );
    v___x_1345_ = lean_uint64_to_nat(v_sys_1313_);
    v___x_1346_ = l_Nat_reprFast(v___x_1345_);
    v___x_1347_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1347_, 0, v___x_1346_);
    v___x_1348_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1348_, 0, v___x_1344_);
    lean_ctor_set(v___x_1348_, 1, v___x_1347_);
    v___x_1349_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1349_, 0, v___x_1348_);
    lean_ctor_set_uint8(
        v___x_1349_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1350_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1350_, 0, v___x_1343_);
    lean_ctor_set(v___x_1350_, 1, v___x_1349_);
    v___x_1351_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1351_, 0, v___x_1350_);
    lean_ctor_set(v___x_1351_, 1, v___x_1326_);
    v___x_1352_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1352_, 0, v___x_1351_);
    lean_ctor_set(v___x_1352_, 1, v___x_1328_);
    v___x_1353_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__11;
    v___x_1354_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1354_, 0, v___x_1352_);
    lean_ctor_set(v___x_1354_, 1, v___x_1353_);
    v___x_1355_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1355_, 0, v___x_1354_);
    lean_ctor_set(v___x_1355_, 1, v___x_1316_);
    v___x_1356_ = lean_uint64_to_nat(v_idle_1314_);
    v___x_1357_ = l_Nat_reprFast(v___x_1356_);
    v___x_1358_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1358_, 0, v___x_1357_);
    v___x_1359_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1359_, 0, v___x_1318_);
    lean_ctor_set(v___x_1359_, 1, v___x_1358_);
    v___x_1360_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1360_, 0, v___x_1359_);
    lean_ctor_set_uint8(
        v___x_1360_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1361_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1361_, 0, v___x_1355_);
    lean_ctor_set(v___x_1361_, 1, v___x_1360_);
    v___x_1362_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1362_, 0, v___x_1361_);
    lean_ctor_set(v___x_1362_, 1, v___x_1326_);
    v___x_1363_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1363_, 0, v___x_1362_);
    lean_ctor_set(v___x_1363_, 1, v___x_1328_);
    v___x_1364_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__13;
    v___x_1365_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1365_, 0, v___x_1363_);
    lean_ctor_set(v___x_1365_, 1, v___x_1364_);
    v___x_1366_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1366_, 0, v___x_1365_);
    lean_ctor_set(v___x_1366_, 1, v___x_1316_);
    v___x_1367_ = lean_uint64_to_nat(v_irq_1315_);
    v___x_1368_ = l_Nat_reprFast(v___x_1367_);
    v___x_1369_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1369_, 0, v___x_1368_);
    v___x_1370_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1370_, 0, v___x_1344_);
    lean_ctor_set(v___x_1370_, 1, v___x_1369_);
    v___x_1371_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1371_, 0, v___x_1370_);
    lean_ctor_set_uint8(
        v___x_1371_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    v___x_1372_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1372_, 0, v___x_1366_);
    lean_ctor_set(v___x_1372_, 1, v___x_1371_);
    v___x_1373_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1374_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1375_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1375_, 0, v___x_1374_);
    lean_ctor_set(v___x_1375_, 1, v___x_1372_);
    v___x_1376_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1377_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1377_, 0, v___x_1375_);
    lean_ctor_set(v___x_1377_, 1, v___x_1376_);
    v___x_1378_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1378_, 0, v___x_1373_);
    lean_ctor_set(v___x_1378_, 1, v___x_1377_);
    v___x_1379_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1379_, 0, v___x_1378_);
    lean_ctor_set_uint8(
        v___x_1379_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1323_,
    );
    return v___x_1379_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___boxed(
    mut v_x_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1381_: *mut LeanObject = core::ptr::null_mut();
    v_res_1381_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(v_x_1380_);
    lean_dec_ref(v_x_1380_);
    return v_res_1381_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr(
    mut v_x_1382_: *mut LeanObject,
    mut v_prec_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(v_x_1382_);
    return v___x_1384_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUTimes_repr___boxed(
    mut v_x_1385_: *mut LeanObject,
    mut v_prec_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1387_: *mut LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Std_Internal_UV_System_instReprCPUTimes_repr(v_x_1385_, v_prec_1386_);
    lean_dec(v_prec_1386_);
    lean_dec_ref(v_x_1385_);
    return v_res_1387_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0()
-> *mut LeanObject {
    let mut v___x_1390_: u64 = 0;
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1390_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1391_ = lean_alloc_ctor(0, 0, (40) as u32);
    lean_ctor_set_uint64(v___x_1391_, 0 as u32, v___x_1390_);
    lean_ctor_set_uint64(v___x_1391_, 8 as u32, v___x_1390_);
    lean_ctor_set_uint64(v___x_1391_, 16 as u32, v___x_1390_);
    lean_ctor_set_uint64(v___x_1391_, 24 as u32, v___x_1390_);
    lean_ctor_set_uint64(v___x_1391_, 32 as u32, v___x_1390_);
    return v___x_1391_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default() -> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    v___x_1392_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default___closed__0,
    );
    return v___x_1392_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUTimes() -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Std_Internal_UV_System_instInhabitedCPUTimes_default;
    return v___x_1393_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg(
    mut v_x_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_model_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_speed_1411_: u64 = 0;
    let mut v_times_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v_model_1410_ = lean_ctor_get(v_x_1409_, 0);
    lean_inc_ref(v_model_1410_);
    v_speed_1411_ = lean_ctor_get_uint64(
        v_x_1409_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_times_1412_ = lean_ctor_get(v_x_1409_, 1);
    lean_inc_ref(v_times_1412_);
    lean_dec_ref(v_x_1409_);
    v___x_1413_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1414_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__3;
    v___x_1415_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18,
    );
    v___x_1416_ = l_String_quote(v_model_1410_);
    v___x_1417_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1417_, 0, v___x_1416_);
    v___x_1418_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1418_, 0, v___x_1415_);
    lean_ctor_set(v___x_1418_, 1, v___x_1417_);
    v___x_1419_ = 0;
    v___x_1420_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1420_, 0, v___x_1418_);
    lean_ctor_set_uint8(
        v___x_1420_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    v___x_1421_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1421_, 0, v___x_1414_);
    lean_ctor_set(v___x_1421_, 1, v___x_1420_);
    v___x_1422_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1423_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1423_, 0, v___x_1421_);
    lean_ctor_set(v___x_1423_, 1, v___x_1422_);
    v___x_1424_ = lean_box(1);
    v___x_1425_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1425_, 0, v___x_1423_);
    lean_ctor_set(v___x_1425_, 1, v___x_1424_);
    v___x_1426_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__5;
    v___x_1427_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1427_, 0, v___x_1425_);
    lean_ctor_set(v___x_1427_, 1, v___x_1426_);
    v___x_1428_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1428_, 0, v___x_1427_);
    lean_ctor_set(v___x_1428_, 1, v___x_1413_);
    v___x_1429_ = lean_uint64_to_nat(v_speed_1411_);
    v___x_1430_ = l_Nat_reprFast(v___x_1429_);
    v___x_1431_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1431_, 0, v___x_1430_);
    v___x_1432_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1432_, 0, v___x_1415_);
    lean_ctor_set(v___x_1432_, 1, v___x_1431_);
    v___x_1433_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1433_, 0, v___x_1432_);
    lean_ctor_set_uint8(
        v___x_1433_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    v___x_1434_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1434_, 0, v___x_1428_);
    lean_ctor_set(v___x_1434_, 1, v___x_1433_);
    v___x_1435_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    lean_ctor_set(v___x_1435_, 1, v___x_1422_);
    v___x_1436_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1436_, 0, v___x_1435_);
    lean_ctor_set(v___x_1436_, 1, v___x_1424_);
    v___x_1437_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg___closed__7;
    v___x_1438_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1438_, 0, v___x_1436_);
    lean_ctor_set(v___x_1438_, 1, v___x_1437_);
    v___x_1439_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    lean_ctor_set(v___x_1439_, 1, v___x_1413_);
    v___x_1440_ = l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg(v_times_1412_);
    lean_dec_ref(v_times_1412_);
    v___x_1441_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1441_, 0, v___x_1415_);
    lean_ctor_set(v___x_1441_, 1, v___x_1440_);
    v___x_1442_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1442_, 0, v___x_1441_);
    lean_ctor_set_uint8(
        v___x_1442_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    v___x_1443_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1443_, 0, v___x_1439_);
    lean_ctor_set(v___x_1443_, 1, v___x_1442_);
    v___x_1444_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1445_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1446_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1446_, 0, v___x_1445_);
    lean_ctor_set(v___x_1446_, 1, v___x_1443_);
    v___x_1447_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1448_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1448_, 0, v___x_1446_);
    lean_ctor_set(v___x_1448_, 1, v___x_1447_);
    v___x_1449_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1449_, 0, v___x_1444_);
    lean_ctor_set(v___x_1449_, 1, v___x_1448_);
    v___x_1450_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1450_, 0, v___x_1449_);
    lean_ctor_set_uint8(
        v___x_1450_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1419_,
    );
    return v___x_1450_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUInfo_repr(
    mut v_x_1451_: *mut LeanObject,
    mut v_prec_1452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    v___x_1453_ = l_Std_Internal_UV_System_instReprCPUInfo_repr___redArg(v_x_1451_);
    return v___x_1453_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprCPUInfo_repr___boxed(
    mut v_x_1454_: *mut LeanObject,
    mut v_prec_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Std_Internal_UV_System_instReprCPUInfo_repr(v_x_1454_, v_prec_1455_);
    lean_dec(v_prec_1455_);
    return v_res_1456_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1()
-> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: u64 = 0;
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1460_ = l_Std_Internal_UV_System_instInhabitedCPUTimes_default;
    v___x_1461_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1462_ = l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0;
    v___x_1463_ = lean_alloc_ctor(0, 2, (8) as u32);
    lean_ctor_set(v___x_1463_, 0, v___x_1462_);
    lean_ctor_set(v___x_1463_, 1, v___x_1460_);
    lean_ctor_set_uint64(
        v___x_1463_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_1461_,
    );
    return v___x_1463_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default() -> *mut LeanObject {
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    v___x_1464_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__1,
    );
    return v___x_1464_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedCPUInfo() -> *mut LeanObject {
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1465_ = l_Std_Internal_UV_System_instInhabitedCPUInfo_default;
    return v___x_1465_;
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
    mut v_x_1472_: *mut LeanObject,
    mut v_x_1473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1478_: u8 = 0;
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u64 = 0;
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1472_) == 0 {
                    v___x_1474_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1;
                    return v___x_1474_;
                } else {
                    v_val_1475_ = lean_ctor_get(v_x_1472_, 0);
                    v_isSharedCheck_1488_ = (!lean_is_exclusive(v_x_1472_)) as u8;
                    if v_isSharedCheck_1488_ == 0 {
                        v___x_1477_ = v_x_1472_;
                        v_isShared_1478_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1475_);
                        lean_dec(v_x_1472_);
                        v___x_1477_ = lean_box(0);
                        v_isShared_1478_ = v_isSharedCheck_1488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1479_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3;
                v___x_1480_ = lean_unbox_uint64(v_val_1475_);
                lean_dec(v_val_1475_);
                v___x_1481_ = lean_uint64_to_nat(v___x_1480_);
                v___x_1482_ = l_Nat_reprFast(v___x_1481_);
                if v_isShared_1478_ == 0 {
                    lean_ctor_set_tag(v___x_1477_, 3);
                    lean_ctor_set(v___x_1477_, 0, v___x_1482_);
                    v___x_1484_ = v___x_1477_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1487_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1482_);
                    v___x_1484_ = v_reuseFailAlloc_1487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1485_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1485_, 0, v___x_1479_);
                lean_ctor_set(v___x_1485_, 1, v___x_1484_);
                v___x_1486_ = l_Repr_addAppParen(v___x_1485_, v_x_1473_);
                return v___x_1486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___boxed(
    mut v_x_1489_: *mut LeanObject,
    mut v_x_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1491_: *mut LeanObject = core::ptr::null_mut();
    v_res_1491_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
        v_x_1489_, v_x_1490_,
    );
    lean_dec(v_x_1490_);
    return v_res_1491_;
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
    mut v_x_1492_: *mut LeanObject,
    mut v_x_1493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1492_) == 0 {
                    v___x_1494_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__1;
                    return v___x_1494_;
                } else {
                    v_val_1495_ = lean_ctor_get(v_x_1492_, 0);
                    v_isSharedCheck_1506_ = (!lean_is_exclusive(v_x_1492_)) as u8;
                    if v_isSharedCheck_1506_ == 0 {
                        v___x_1497_ = v_x_1492_;
                        v_isShared_1498_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1495_);
                        lean_dec(v_x_1492_);
                        v___x_1497_ = lean_box(0);
                        v_isShared_1498_ = v_isSharedCheck_1506_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1499_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0___closed__3;
                v___x_1500_ = l_String_quote(v_val_1495_);
                if v_isShared_1498_ == 0 {
                    lean_ctor_set_tag(v___x_1497_, 3);
                    lean_ctor_set(v___x_1497_, 0, v___x_1500_);
                    v___x_1502_ = v___x_1497_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1505_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1500_);
                    v___x_1502_ = v_reuseFailAlloc_1505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1503_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1503_, 0, v___x_1499_);
                lean_ctor_set(v___x_1503_, 1, v___x_1502_);
                v___x_1504_ = l_Repr_addAppParen(v___x_1503_, v_x_1493_);
                return v___x_1504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1___boxed(
    mut v_x_1507_: *mut LeanObject,
    mut v_x_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1509_: *mut LeanObject = core::ptr::null_mut();
    v_res_1509_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
        v_x_1507_, v_x_1508_,
    );
    lean_dec(v_x_1508_);
    return v_res_1509_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg(
    mut v_x_1531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_username_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uid_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gid_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_shell_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_homedir_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v_username_1532_ = lean_ctor_get(v_x_1531_, 0);
    lean_inc_ref(v_username_1532_);
    v_uid_1533_ = lean_ctor_get(v_x_1531_, 1);
    lean_inc(v_uid_1533_);
    v_gid_1534_ = lean_ctor_get(v_x_1531_, 2);
    lean_inc(v_gid_1534_);
    v_shell_1535_ = lean_ctor_get(v_x_1531_, 3);
    lean_inc(v_shell_1535_);
    v_homedir_1536_ = lean_ctor_get(v_x_1531_, 4);
    lean_inc(v_homedir_1536_);
    lean_dec_ref(v_x_1531_);
    v___x_1537_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1538_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__3;
    v___x_1539_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__7,
    );
    v___x_1540_ = l_String_quote(v_username_1532_);
    v___x_1541_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1541_, 0, v___x_1540_);
    v___x_1542_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1542_, 0, v___x_1539_);
    lean_ctor_set(v___x_1542_, 1, v___x_1541_);
    v___x_1543_ = 0;
    v___x_1544_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1544_, 0, v___x_1542_);
    lean_ctor_set_uint8(
        v___x_1544_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1545_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1545_, 0, v___x_1538_);
    lean_ctor_set(v___x_1545_, 1, v___x_1544_);
    v___x_1546_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1547_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1547_, 0, v___x_1545_);
    lean_ctor_set(v___x_1547_, 1, v___x_1546_);
    v___x_1548_ = lean_box(1);
    v___x_1549_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1549_, 0, v___x_1547_);
    lean_ctor_set(v___x_1549_, 1, v___x_1548_);
    v___x_1550_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__5;
    v___x_1551_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1551_, 0, v___x_1549_);
    lean_ctor_set(v___x_1551_, 1, v___x_1550_);
    v___x_1552_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1552_, 0, v___x_1551_);
    lean_ctor_set(v___x_1552_, 1, v___x_1537_);
    v___x_1553_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9,
    );
    v___x_1554_ = lean_unsigned_to_nat(0);
    v___x_1555_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
        v_uid_1533_,
        v___x_1554_,
    );
    v___x_1556_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1556_, 0, v___x_1553_);
    lean_ctor_set(v___x_1556_, 1, v___x_1555_);
    v___x_1557_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1557_, 0, v___x_1556_);
    lean_ctor_set_uint8(
        v___x_1557_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1558_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1558_, 0, v___x_1552_);
    lean_ctor_set(v___x_1558_, 1, v___x_1557_);
    v___x_1559_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1559_, 0, v___x_1558_);
    lean_ctor_set(v___x_1559_, 1, v___x_1546_);
    v___x_1560_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1560_, 0, v___x_1559_);
    lean_ctor_set(v___x_1560_, 1, v___x_1548_);
    v___x_1561_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7;
    v___x_1562_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1562_, 0, v___x_1560_);
    lean_ctor_set(v___x_1562_, 1, v___x_1561_);
    v___x_1563_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1563_, 0, v___x_1562_);
    lean_ctor_set(v___x_1563_, 1, v___x_1537_);
    v___x_1564_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__0(
        v_gid_1534_,
        v___x_1554_,
    );
    v___x_1565_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1565_, 0, v___x_1553_);
    lean_ctor_set(v___x_1565_, 1, v___x_1564_);
    v___x_1566_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1566_, 0, v___x_1565_);
    lean_ctor_set_uint8(
        v___x_1566_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1567_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1567_, 0, v___x_1563_);
    lean_ctor_set(v___x_1567_, 1, v___x_1566_);
    v___x_1568_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1568_, 0, v___x_1567_);
    lean_ctor_set(v___x_1568_, 1, v___x_1546_);
    v___x_1569_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1569_, 0, v___x_1568_);
    lean_ctor_set(v___x_1569_, 1, v___x_1548_);
    v___x_1570_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__9;
    v___x_1571_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1571_, 0, v___x_1569_);
    lean_ctor_set(v___x_1571_, 1, v___x_1570_);
    v___x_1572_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1572_, 0, v___x_1571_);
    lean_ctor_set(v___x_1572_, 1, v___x_1537_);
    v___x_1573_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__18,
    );
    v___x_1574_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
        v_shell_1535_,
        v___x_1554_,
    );
    v___x_1575_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1575_, 0, v___x_1573_);
    lean_ctor_set(v___x_1575_, 1, v___x_1574_);
    v___x_1576_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1576_, 0, v___x_1575_);
    lean_ctor_set_uint8(
        v___x_1576_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1577_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1577_, 0, v___x_1572_);
    lean_ctor_set(v___x_1577_, 1, v___x_1576_);
    v___x_1578_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1578_, 0, v___x_1577_);
    lean_ctor_set(v___x_1578_, 1, v___x_1546_);
    v___x_1579_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1579_, 0, v___x_1578_);
    lean_ctor_set(v___x_1579_, 1, v___x_1548_);
    v___x_1580_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__11;
    v___x_1581_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1581_, 0, v___x_1579_);
    lean_ctor_set(v___x_1581_, 1, v___x_1580_);
    v___x_1582_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1582_, 0, v___x_1581_);
    lean_ctor_set(v___x_1582_, 1, v___x_1537_);
    v___x_1583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1584_ = l_Option_repr___at___00Std_Internal_UV_System_instReprPasswdInfo_repr_spec__1(
        v_homedir_1536_,
        v___x_1554_,
    );
    v___x_1585_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1585_, 0, v___x_1583_);
    lean_ctor_set(v___x_1585_, 1, v___x_1584_);
    v___x_1586_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1586_, 0, v___x_1585_);
    lean_ctor_set_uint8(
        v___x_1586_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    v___x_1587_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1587_, 0, v___x_1582_);
    lean_ctor_set(v___x_1587_, 1, v___x_1586_);
    v___x_1588_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1589_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1590_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1590_, 0, v___x_1589_);
    lean_ctor_set(v___x_1590_, 1, v___x_1587_);
    v___x_1591_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1592_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1592_, 0, v___x_1590_);
    lean_ctor_set(v___x_1592_, 1, v___x_1591_);
    v___x_1593_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1593_, 0, v___x_1588_);
    lean_ctor_set(v___x_1593_, 1, v___x_1592_);
    v___x_1594_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1594_, 0, v___x_1593_);
    lean_ctor_set_uint8(
        v___x_1594_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1543_,
    );
    return v___x_1594_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprPasswdInfo_repr(
    mut v_x_1595_: *mut LeanObject,
    mut v_prec_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg(v_x_1595_);
    return v___x_1597_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprPasswdInfo_repr___boxed(
    mut v_x_1598_: *mut LeanObject,
    mut v_prec_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1600_: *mut LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr(v_x_1598_, v_prec_1599_);
    lean_dec(v_prec_1599_);
    return v_res_1600_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_1608_: *mut LeanObject,
    mut v_x_1609_: *mut LeanObject,
    mut v_x_1610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1610_) == 0 {
                    lean_dec(v_x_1608_);
                    return v_x_1609_;
                } else {
                    v_head_1611_ = lean_ctor_get(v_x_1610_, 0);
                    v_tail_1612_ = lean_ctor_get(v_x_1610_, 1);
                    v_isSharedCheck_1623_ = (!lean_is_exclusive(v_x_1610_)) as u8;
                    if v_isSharedCheck_1623_ == 0 {
                        v___x_1614_ = v_x_1610_;
                        v_isShared_1615_ = v_isSharedCheck_1623_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1612_);
                        lean_inc(v_head_1611_);
                        lean_dec(v_x_1610_);
                        v___x_1614_ = lean_box(0);
                        v_isShared_1615_ = v_isSharedCheck_1623_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1608_);
                if v_isShared_1615_ == 0 {
                    lean_ctor_set_tag(v___x_1614_, 5);
                    lean_ctor_set(v___x_1614_, 1, v_x_1608_);
                    lean_ctor_set(v___x_1614_, 0, v_x_1609_);
                    v___x_1617_ = v___x_1614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1622_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_x_1609_);
                    lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_x_1608_);
                    v___x_1617_ = v_reuseFailAlloc_1622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1618_ = l_String_quote(v_head_1611_);
                v___x_1619_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1619_, 0, v___x_1618_);
                v___x_1620_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1620_, 0, v___x_1617_);
                lean_ctor_set(v___x_1620_, 1, v___x_1619_);
                v_x_1609_ = v___x_1620_;
                v_x_1610_ = v_tail_1612_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(
    mut v_x_1624_: *mut LeanObject,
    mut v_x_1625_: *mut LeanObject,
    mut v_x_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1626_) == 0 {
                    lean_dec(v_x_1624_);
                    return v_x_1625_;
                } else {
                    v_head_1627_ = lean_ctor_get(v_x_1626_, 0);
                    v_tail_1628_ = lean_ctor_get(v_x_1626_, 1);
                    v_isSharedCheck_1639_ = (!lean_is_exclusive(v_x_1626_)) as u8;
                    if v_isSharedCheck_1639_ == 0 {
                        v___x_1630_ = v_x_1626_;
                        v_isShared_1631_ = v_isSharedCheck_1639_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1628_);
                        lean_inc(v_head_1627_);
                        lean_dec(v_x_1626_);
                        v___x_1630_ = lean_box(0);
                        v_isShared_1631_ = v_isSharedCheck_1639_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1624_);
                if v_isShared_1631_ == 0 {
                    lean_ctor_set_tag(v___x_1630_, 5);
                    lean_ctor_set(v___x_1630_, 1, v_x_1624_);
                    lean_ctor_set(v___x_1630_, 0, v_x_1625_);
                    v___x_1633_ = v___x_1630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1638_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_x_1625_);
                    lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_x_1624_);
                    v___x_1633_ = v_reuseFailAlloc_1638_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1634_ = l_String_quote(v_head_1627_);
                v___x_1635_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1635_, 0, v___x_1634_);
                v___x_1636_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1636_, 0, v___x_1633_);
                lean_ctor_set(v___x_1636_, 1, v___x_1635_);
                v___x_1637_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1_spec__2(v_x_1624_, v___x_1636_, v_tail_1628_);
                return v___x_1637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(
    mut v___y_1640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___x_1641_ = l_String_quote(v___y_1640_);
    v___x_1642_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1642_, 0, v___x_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0(
    mut v_x_1643_: *mut LeanObject,
    mut v_x_1644_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1643_) == 0 {
        let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1644_);
        v___x_1645_ = lean_box(0);
        return v___x_1645_;
    } else {
        let mut v_tail_1646_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1646_ = lean_ctor_get(v_x_1643_, 1);
        if lean_obj_tag(v_tail_1646_) == 0 {
            let mut v_head_1647_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_1644_);
            v_head_1647_ = lean_ctor_get(v_x_1643_, 0);
            lean_inc(v_head_1647_);
            lean_dec_ref_known(v_x_1643_, 2);
            v___x_1648_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1647_);
            return v___x_1648_;
        } else {
            let mut v_head_1649_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_1646_);
            v_head_1649_ = lean_ctor_get(v_x_1643_, 0);
            lean_inc(v_head_1649_);
            lean_dec_ref_known(v_x_1643_, 2);
            v___x_1650_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0___lam__0(v_head_1649_);
            v___x_1651_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0_spec__1(v_x_1644_, v___x_1650_, v_tail_1646_);
            return v___x_1651_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1657_ =
        l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__0;
    v___x_1658_ = lean_string_length(v___x_1657_);
    return v___x_1658_;
}
pub unsafe fn _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3_once), _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__3);
    v___x_1660_ = lean_nat_to_int(v___x_1659_);
    return v___x_1660_;
}
pub unsafe fn l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0(
    mut v_xs_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: u8 = 0;
    v___x_1669_ = lean_array_get_size(v_xs_1668_);
    v___x_1670_ = lean_unsigned_to_nat(0);
    v___x_1671_ = lean_nat_dec_eq(v___x_1669_, v___x_1670_);
    if v___x_1671_ == 0 {
        let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
        v___x_1672_ = lean_array_to_list(v_xs_1668_);
        v___x_1673_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__1;
        v___x_1674_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0_spec__0(v___x_1672_, v___x_1673_);
        v___x_1675_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4_once), _init_l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__4);
        v___x_1676_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__5;
        v___x_1677_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_1677_, 0, v___x_1676_);
        lean_ctor_set(v___x_1677_, 1, v___x_1674_);
        v___x_1678_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__6;
        v___x_1679_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_1679_, 0, v___x_1677_);
        lean_ctor_set(v___x_1679_, 1, v___x_1678_);
        v___x_1680_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_1680_, 0, v___x_1675_);
        lean_ctor_set(v___x_1680_, 1, v___x_1679_);
        v___x_1681_ = l_Std_Format_fill(v___x_1680_);
        return v___x_1681_;
    } else {
        let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_1668_);
        v___x_1682_ =
            l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0___closed__8;
        return v___x_1682_;
    }
}
pub unsafe fn _init_l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1692_ = lean_unsigned_to_nat(13);
    v___x_1693_ = lean_nat_to_int(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg(
    mut v_x_1697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_groupname_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gid_1699_: u64 = 0;
    let mut v_members_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    v_groupname_1698_ = lean_ctor_get(v_x_1697_, 0);
    lean_inc_ref(v_groupname_1698_);
    v_gid_1699_ = lean_ctor_get_uint64(
        v_x_1697_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    v_members_1700_ = lean_ctor_get(v_x_1697_, 1);
    lean_inc_ref(v_members_1700_);
    lean_dec_ref(v_x_1697_);
    v___x_1701_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1702_ = l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__3;
    v___x_1703_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4_once
        ),
        _init_l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__4,
    );
    v___x_1704_ = l_String_quote(v_groupname_1698_);
    v___x_1705_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1705_, 0, v___x_1704_);
    v___x_1706_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1706_, 0, v___x_1703_);
    lean_ctor_set(v___x_1706_, 1, v___x_1705_);
    v___x_1707_ = 0;
    v___x_1708_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1708_, 0, v___x_1706_);
    lean_ctor_set_uint8(
        v___x_1708_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    v___x_1709_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1709_, 0, v___x_1702_);
    lean_ctor_set(v___x_1709_, 1, v___x_1708_);
    v___x_1710_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1711_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1711_, 0, v___x_1709_);
    lean_ctor_set(v___x_1711_, 1, v___x_1710_);
    v___x_1712_ = lean_box(1);
    v___x_1713_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1713_, 0, v___x_1711_);
    lean_ctor_set(v___x_1713_, 1, v___x_1712_);
    v___x_1714_ = l_Std_Internal_UV_System_instReprPasswdInfo_repr___redArg___closed__7;
    v___x_1715_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1715_, 0, v___x_1713_);
    lean_ctor_set(v___x_1715_, 1, v___x_1714_);
    v___x_1716_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1716_, 0, v___x_1715_);
    lean_ctor_set(v___x_1716_, 1, v___x_1701_);
    v___x_1717_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9_once
        ),
        _init_l_Std_Internal_UV_System_instReprCPUTimes_repr___redArg___closed__9,
    );
    v___x_1718_ = lean_uint64_to_nat(v_gid_1699_);
    v___x_1719_ = l_Nat_reprFast(v___x_1718_);
    v___x_1720_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1720_, 0, v___x_1719_);
    v___x_1721_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1721_, 0, v___x_1717_);
    lean_ctor_set(v___x_1721_, 1, v___x_1720_);
    v___x_1722_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1722_, 0, v___x_1721_);
    lean_ctor_set_uint8(
        v___x_1722_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    v___x_1723_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1723_, 0, v___x_1716_);
    lean_ctor_set(v___x_1723_, 1, v___x_1722_);
    v___x_1724_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1724_, 0, v___x_1723_);
    lean_ctor_set(v___x_1724_, 1, v___x_1710_);
    v___x_1725_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1725_, 0, v___x_1724_);
    lean_ctor_set(v___x_1725_, 1, v___x_1712_);
    v___x_1726_ = l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg___closed__6;
    v___x_1727_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1727_, 0, v___x_1725_);
    lean_ctor_set(v___x_1727_, 1, v___x_1726_);
    v___x_1728_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1728_, 0, v___x_1727_);
    lean_ctor_set(v___x_1728_, 1, v___x_1701_);
    v___x_1729_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1730_ = l_Array_repr___at___00Std_Internal_UV_System_instReprGroupInfo_repr_spec__0(
        v_members_1700_,
    );
    v___x_1731_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1731_, 0, v___x_1729_);
    lean_ctor_set(v___x_1731_, 1, v___x_1730_);
    v___x_1732_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1732_, 0, v___x_1731_);
    lean_ctor_set_uint8(
        v___x_1732_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    v___x_1733_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1733_, 0, v___x_1728_);
    lean_ctor_set(v___x_1733_, 1, v___x_1732_);
    v___x_1734_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1735_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1736_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1736_, 0, v___x_1735_);
    lean_ctor_set(v___x_1736_, 1, v___x_1733_);
    v___x_1737_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1738_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1738_, 0, v___x_1736_);
    lean_ctor_set(v___x_1738_, 1, v___x_1737_);
    v___x_1739_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1739_, 0, v___x_1734_);
    lean_ctor_set(v___x_1739_, 1, v___x_1738_);
    v___x_1740_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1740_, 0, v___x_1739_);
    lean_ctor_set_uint8(
        v___x_1740_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1707_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprGroupInfo_repr(
    mut v_x_1741_: *mut LeanObject,
    mut v_prec_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v___x_1743_ = l_Std_Internal_UV_System_instReprGroupInfo_repr___redArg(v_x_1741_);
    return v___x_1743_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprGroupInfo_repr___boxed(
    mut v_x_1744_: *mut LeanObject,
    mut v_prec_1745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1746_: *mut LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Std_Internal_UV_System_instReprGroupInfo_repr(v_x_1744_, v_prec_1745_);
    lean_dec(v_prec_1745_);
    return v_res_1746_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1()
-> *mut LeanObject {
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: u64 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v___x_1751_ = l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__0;
    v___x_1752_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default___closed__0,
    );
    v___x_1753_ = l_Std_Internal_UV_System_instInhabitedCPUInfo_default___closed__0;
    v___x_1754_ = lean_alloc_ctor(0, 2, (8) as u32);
    lean_ctor_set(v___x_1754_, 0, v___x_1753_);
    lean_ctor_set(v___x_1754_, 1, v___x_1751_);
    lean_ctor_set_uint64(
        v___x_1754_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_1752_,
    );
    return v___x_1754_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default() -> *mut LeanObject {
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    v___x_1755_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1_once
        ),
        _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default___closed__1,
    );
    return v___x_1755_;
}
pub unsafe fn _init_l_Std_Internal_UV_System_instInhabitedGroupInfo() -> *mut LeanObject {
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Std_Internal_UV_System_instInhabitedGroupInfo_default;
    return v___x_1756_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg(
    mut v_x_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sysname_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_release_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_version_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_machine_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v_sysname_1776_ = lean_ctor_get(v_x_1775_, 0);
    lean_inc_ref(v_sysname_1776_);
    v_release_1777_ = lean_ctor_get(v_x_1775_, 1);
    lean_inc_ref(v_release_1777_);
    v_version_1778_ = lean_ctor_get(v_x_1775_, 2);
    lean_inc_ref(v_version_1778_);
    v_machine_1779_ = lean_ctor_get(v_x_1775_, 3);
    lean_inc_ref(v_machine_1779_);
    lean_dec_ref(v_x_1775_);
    v___x_1780_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__5;
    v___x_1781_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__3;
    v___x_1782_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__31,
    );
    v___x_1783_ = l_String_quote(v_sysname_1776_);
    v___x_1784_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1784_, 0, v___x_1783_);
    v___x_1785_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1785_, 0, v___x_1782_);
    lean_ctor_set(v___x_1785_, 1, v___x_1784_);
    v___x_1786_ = 0;
    v___x_1787_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1787_, 0, v___x_1785_);
    lean_ctor_set_uint8(
        v___x_1787_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1788_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1788_, 0, v___x_1781_);
    lean_ctor_set(v___x_1788_, 1, v___x_1787_);
    v___x_1789_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__9;
    v___x_1790_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1790_, 0, v___x_1788_);
    lean_ctor_set(v___x_1790_, 1, v___x_1789_);
    v___x_1791_ = lean_box(1);
    v___x_1792_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1792_, 0, v___x_1790_);
    lean_ctor_set(v___x_1792_, 1, v___x_1791_);
    v___x_1793_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__5;
    v___x_1794_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1794_, 0, v___x_1792_);
    lean_ctor_set(v___x_1794_, 1, v___x_1793_);
    v___x_1795_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1795_, 0, v___x_1794_);
    lean_ctor_set(v___x_1795_, 1, v___x_1780_);
    v___x_1796_ = l_String_quote(v_release_1777_);
    v___x_1797_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1797_, 0, v___x_1796_);
    v___x_1798_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1798_, 0, v___x_1782_);
    lean_ctor_set(v___x_1798_, 1, v___x_1797_);
    v___x_1799_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1799_, 0, v___x_1798_);
    lean_ctor_set_uint8(
        v___x_1799_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1800_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1800_, 0, v___x_1795_);
    lean_ctor_set(v___x_1800_, 1, v___x_1799_);
    v___x_1801_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1801_, 0, v___x_1800_);
    lean_ctor_set(v___x_1801_, 1, v___x_1789_);
    v___x_1802_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1802_, 0, v___x_1801_);
    lean_ctor_set(v___x_1802_, 1, v___x_1791_);
    v___x_1803_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__7;
    v___x_1804_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1804_, 0, v___x_1802_);
    lean_ctor_set(v___x_1804_, 1, v___x_1803_);
    v___x_1805_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1805_, 0, v___x_1804_);
    lean_ctor_set(v___x_1805_, 1, v___x_1780_);
    v___x_1806_ = l_String_quote(v_version_1778_);
    v___x_1807_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1807_, 0, v___x_1806_);
    v___x_1808_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1808_, 0, v___x_1782_);
    lean_ctor_set(v___x_1808_, 1, v___x_1807_);
    v___x_1809_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1809_, 0, v___x_1808_);
    lean_ctor_set_uint8(
        v___x_1809_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1810_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1810_, 0, v___x_1805_);
    lean_ctor_set(v___x_1810_, 1, v___x_1809_);
    v___x_1811_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    lean_ctor_set(v___x_1811_, 1, v___x_1789_);
    v___x_1812_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    lean_ctor_set(v___x_1812_, 1, v___x_1791_);
    v___x_1813_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg___closed__9;
    v___x_1814_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1814_, 0, v___x_1812_);
    lean_ctor_set(v___x_1814_, 1, v___x_1813_);
    v___x_1815_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    lean_ctor_set(v___x_1815_, 1, v___x_1780_);
    v___x_1816_ = l_String_quote(v_machine_1779_);
    v___x_1817_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1817_, 0, v___x_1816_);
    v___x_1818_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1818_, 0, v___x_1782_);
    lean_ctor_set(v___x_1818_, 1, v___x_1817_);
    v___x_1819_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1819_, 0, v___x_1818_);
    lean_ctor_set_uint8(
        v___x_1819_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    v___x_1820_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1820_, 0, v___x_1815_);
    lean_ctor_set(v___x_1820_, 1, v___x_1819_);
    v___x_1821_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48),
        core::ptr::addr_of_mut!(
            l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48_once
        ),
        _init_l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__48,
    );
    v___x_1822_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__49;
    v___x_1823_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1823_, 0, v___x_1822_);
    lean_ctor_set(v___x_1823_, 1, v___x_1820_);
    v___x_1824_ = l_Std_Internal_UV_System_instReprRUsage_repr___redArg___closed__50;
    v___x_1825_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1825_, 0, v___x_1823_);
    lean_ctor_set(v___x_1825_, 1, v___x_1824_);
    v___x_1826_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1826_, 0, v___x_1821_);
    lean_ctor_set(v___x_1826_, 1, v___x_1825_);
    v___x_1827_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1827_, 0, v___x_1826_);
    lean_ctor_set_uint8(
        v___x_1827_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1786_,
    );
    return v___x_1827_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprUnameInfo_repr(
    mut v_x_1828_: *mut LeanObject,
    mut v_prec_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Std_Internal_UV_System_instReprUnameInfo_repr___redArg(v_x_1828_);
    return v___x_1830_;
}
pub unsafe fn l_Std_Internal_UV_System_instReprUnameInfo_repr___boxed(
    mut v_x_1831_: *mut LeanObject,
    mut v_prec_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1833_: *mut LeanObject = core::ptr::null_mut();
    v_res_1833_ = l_Std_Internal_UV_System_instReprUnameInfo_repr(v_x_1831_, v_prec_1832_);
    lean_dec(v_prec_1832_);
    return v_res_1833_;
}
pub unsafe fn l_Std_Internal_UV_System_getProcessTitle___boxed(
    mut v_a_00___x40___internal___hyg_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1842_: *mut LeanObject = core::ptr::null_mut();
    v_res_1842_ = lean_uv_get_process_title();
    return v_res_1842_;
}
pub unsafe fn l_Std_Internal_UV_System_setProcessTitle___boxed(
    mut v_a_00___x40___internal___hyg_1845_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1847_ = lean_uv_set_process_title(v_a_00___x40___internal___hyg_1845_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1845_);
    return v_res_1847_;
}
pub unsafe fn l_Std_Internal_UV_System_uptime___boxed(
    mut v_a_00___x40___internal___hyg_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1850_: *mut LeanObject = core::ptr::null_mut();
    v_res_1850_ = lean_uv_uptime();
    return v_res_1850_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPid___boxed(
    mut v_a_00___x40___internal___hyg_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1853_: *mut LeanObject = core::ptr::null_mut();
    v_res_1853_ = lean_uv_os_getpid();
    return v_res_1853_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPpid___boxed(
    mut v_a_00___x40___internal___hyg_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1856_: *mut LeanObject = core::ptr::null_mut();
    v_res_1856_ = lean_uv_os_getppid();
    return v_res_1856_;
}
pub unsafe fn l_Std_Internal_UV_System_cpuInfo___boxed(
    mut v_a_00___x40___internal___hyg_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1859_: *mut LeanObject = core::ptr::null_mut();
    v_res_1859_ = lean_uv_cpu_info();
    return v_res_1859_;
}
pub unsafe fn l_Std_Internal_UV_System_cwd___boxed(
    mut v_a_00___x40___internal___hyg_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1862_: *mut LeanObject = core::ptr::null_mut();
    v_res_1862_ = lean_uv_cwd();
    return v_res_1862_;
}
pub unsafe fn l_Std_Internal_UV_System_chdir___boxed(
    mut v_a_00___x40___internal___hyg_1865_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1867_: *mut LeanObject = core::ptr::null_mut();
    v_res_1867_ = lean_uv_chdir(v_a_00___x40___internal___hyg_1865_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1865_);
    return v_res_1867_;
}
pub unsafe fn l_Std_Internal_UV_System_osHomedir___boxed(
    mut v_a_00___x40___internal___hyg_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1870_: *mut LeanObject = core::ptr::null_mut();
    v_res_1870_ = lean_uv_os_homedir();
    return v_res_1870_;
}
pub unsafe fn l_Std_Internal_UV_System_osTmpdir___boxed(
    mut v_a_00___x40___internal___hyg_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1873_: *mut LeanObject = core::ptr::null_mut();
    v_res_1873_ = lean_uv_os_tmpdir();
    return v_res_1873_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPasswd___boxed(
    mut v_a_00___x40___internal___hyg_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1876_: *mut LeanObject = core::ptr::null_mut();
    v_res_1876_ = lean_uv_os_get_passwd();
    return v_res_1876_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetGroup___boxed(
    mut v_a_00___x40___internal___hyg_1879_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1881_: u64 = 0;
    let mut v_res_1882_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1881_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_1879_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1879_);
    v_res_1882_ = lean_uv_os_get_group(v_a_00___x40___internal___hyg_1__boxed_1881_);
    return v_res_1882_;
}
pub unsafe fn l_Std_Internal_UV_System_osEnviron___boxed(
    mut v_a_00___x40___internal___hyg_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1885_: *mut LeanObject = core::ptr::null_mut();
    v_res_1885_ = lean_uv_os_environ();
    return v_res_1885_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetenv___boxed(
    mut v_a_00___x40___internal___hyg_1888_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1890_: *mut LeanObject = core::ptr::null_mut();
    v_res_1890_ = lean_uv_os_getenv(v_a_00___x40___internal___hyg_1888_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1888_);
    return v_res_1890_;
}
pub unsafe fn l_Std_Internal_UV_System_osSetenv___boxed(
    mut v_a_00___x40___internal___hyg_1894_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1895_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1897_: *mut LeanObject = core::ptr::null_mut();
    v_res_1897_ = lean_uv_os_setenv(
        v_a_00___x40___internal___hyg_1894_,
        v_a_00___x40___internal___hyg_1895_,
    );
    lean_dec_ref(v_a_00___x40___internal___hyg_1895_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1894_);
    return v_res_1897_;
}
pub unsafe fn l_Std_Internal_UV_System_osUnsetenv___boxed(
    mut v_a_00___x40___internal___hyg_1900_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1902_: *mut LeanObject = core::ptr::null_mut();
    v_res_1902_ = lean_uv_os_unsetenv(v_a_00___x40___internal___hyg_1900_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1900_);
    return v_res_1902_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetHostname___boxed(
    mut v_a_00___x40___internal___hyg_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1905_: *mut LeanObject = core::ptr::null_mut();
    v_res_1905_ = lean_uv_os_gethostname();
    return v_res_1905_;
}
pub unsafe fn l_Std_Internal_UV_System_osGetPriority___boxed(
    mut v_a_00___x40___internal___hyg_1908_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1910_: u64 = 0;
    let mut v_res_1911_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1910_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_1908_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1908_);
    v_res_1911_ = lean_uv_os_getpriority(v_a_00___x40___internal___hyg_1__boxed_1910_);
    return v_res_1911_;
}
pub unsafe fn l_Std_Internal_UV_System_osSetPriority___boxed(
    mut v_a_00___x40___internal___hyg_1915_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1916_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1918_: u64 = 0;
    let mut v_a_00___x40___internal___hyg_2__boxed_1919_: u64 = 0;
    let mut v_res_1920_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1918_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_1915_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1915_);
    v_a_00___x40___internal___hyg_2__boxed_1919_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_1916_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1916_);
    v_res_1920_ = lean_uv_os_setpriority(
        v_a_00___x40___internal___hyg_1__boxed_1918_,
        v_a_00___x40___internal___hyg_2__boxed_1919_,
    );
    return v_res_1920_;
}
pub unsafe fn l_Std_Internal_UV_System_osUname___boxed(
    mut v_a_00___x40___internal___hyg_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1923_ = lean_uv_os_uname();
    return v_res_1923_;
}
pub unsafe fn l_Std_Internal_UV_System_hrtime___boxed(
    mut v_a_00___x40___internal___hyg_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1926_: *mut LeanObject = core::ptr::null_mut();
    v_res_1926_ = lean_uv_hrtime();
    return v_res_1926_;
}
pub unsafe fn l_Std_Internal_UV_System_random___boxed(
    mut v_a_00___x40___internal___hyg_1929_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_1931_: u64 = 0;
    let mut v_res_1932_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_1931_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_1929_);
    lean_dec_ref(v_a_00___x40___internal___hyg_1929_);
    v_res_1932_ = lean_uv_random(v_a_00___x40___internal___hyg_1__boxed_1931_);
    return v_res_1932_;
}
pub unsafe fn l_Std_Internal_UV_System_getrusage___boxed(
    mut v_a_00___x40___internal___hyg_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1935_: *mut LeanObject = core::ptr::null_mut();
    v_res_1935_ = lean_uv_getrusage();
    return v_res_1935_;
}
pub unsafe fn l_Std_Internal_UV_System_exePath___boxed(
    mut v_a_00___x40___internal___hyg_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1938_: *mut LeanObject = core::ptr::null_mut();
    v_res_1938_ = lean_uv_exepath();
    return v_res_1938_;
}
pub unsafe fn l_Std_Internal_UV_System_freeMemory___boxed(
    mut v_a_00___x40___internal___hyg_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1941_: *mut LeanObject = core::ptr::null_mut();
    v_res_1941_ = lean_uv_get_free_memory();
    return v_res_1941_;
}
pub unsafe fn l_Std_Internal_UV_System_totalMemory___boxed(
    mut v_a_00___x40___internal___hyg_1943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1944_: *mut LeanObject = core::ptr::null_mut();
    v_res_1944_ = lean_uv_get_total_memory();
    return v_res_1944_;
}
pub unsafe fn l_Std_Internal_UV_System_constrainedMemory___boxed(
    mut v_a_00___x40___internal___hyg_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1947_: *mut LeanObject = core::ptr::null_mut();
    v_res_1947_ = lean_uv_get_constrained_memory();
    return v_res_1947_;
}
pub unsafe fn l_Std_Internal_UV_System_availableMemory___boxed(
    mut v_a_00___x40___internal___hyg_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1950_: *mut LeanObject = core::ptr::null_mut();
    v_res_1950_ = lean_uv_get_available_memory();
    return v_res_1950_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_UV_System(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_SInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Net(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Internal_UV_System_instInhabitedRUsage_default =
        _init_l_Std_Internal_UV_System_instInhabitedRUsage_default();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedRUsage_default);
    l_Std_Internal_UV_System_instInhabitedRUsage =
        _init_l_Std_Internal_UV_System_instInhabitedRUsage();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedRUsage);
    l_Std_Internal_UV_System_instInhabitedCPUTimes_default =
        _init_l_Std_Internal_UV_System_instInhabitedCPUTimes_default();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUTimes_default);
    l_Std_Internal_UV_System_instInhabitedCPUTimes =
        _init_l_Std_Internal_UV_System_instInhabitedCPUTimes();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUTimes);
    l_Std_Internal_UV_System_instInhabitedCPUInfo_default =
        _init_l_Std_Internal_UV_System_instInhabitedCPUInfo_default();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUInfo_default);
    l_Std_Internal_UV_System_instInhabitedCPUInfo =
        _init_l_Std_Internal_UV_System_instInhabitedCPUInfo();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedCPUInfo);
    l_Std_Internal_UV_System_instInhabitedGroupInfo_default =
        _init_l_Std_Internal_UV_System_instInhabitedGroupInfo_default();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedGroupInfo_default);
    l_Std_Internal_UV_System_instInhabitedGroupInfo =
        _init_l_Std_Internal_UV_System_instInhabitedGroupInfo();
    lean_mark_persistent(l_Std_Internal_UV_System_instInhabitedGroupInfo);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_UV_System(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Internal_UV_System(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_Promise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_SInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Net(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_System(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Internal_UV_System(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Internal_UV_System(builtin);
}
