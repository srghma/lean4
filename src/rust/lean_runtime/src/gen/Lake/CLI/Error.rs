// Lean compiler output
// Module: Lake.CLI.Error
// Imports: Init.Data.ToString Init.System.FilePath
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Char_quote, l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::System::FilePath::{
    initialize_Init_System_FilePath, runtime_initialize_Init_System_FilePath,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{lean_string_length, lean_string_push};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_nat_dec_le, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_box_uint32, lean_ctor_get, lean_ctor_get_uint32, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static mut l_Lake_instInhabitedCliError_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_instInhabitedCliError: *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [91, 93, 0]};
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0_value
) as *mut LeanObject;
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1_value
) as *mut LeanObject;
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2_value
) as *mut LeanObject;
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3_value
) as *mut LeanObject;
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__3_value) as *mut LeanObject] };
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4_value
) as *mut LeanObject;
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__4_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5_value
) as *mut LeanObject;
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6_value
) as *mut LeanObject;
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7:
    *mut LeanObject = core::ptr::null_mut();
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2_value) as *mut LeanObject] };
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9_value
) as *mut LeanObject;
pub static l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__6_value) as *mut LeanObject] };
static mut l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10_value
) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__0_value: LeanStringObject<33> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 76, 97, 107, 101, 73, 110, 115, 116, 97, 108, 108, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__2_value: LeanStringObject<33> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 76, 101, 97, 110, 73, 110, 115, 116, 97, 108, 108, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__4_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 109, 105, 115, 115,
            105, 110, 103, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__6_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 101, 120,
            112, 101, 99, 116, 101, 100, 80, 108, 117, 115, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__7_value) as *mut LeanObject;
static mut l_Lake_instReprCliError_repr___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprCliError_repr___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_instReprCliError_repr___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprCliError_repr___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprCliError_repr___closed__10_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 67, 111, 109, 109, 97, 110, 100, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__10_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__11_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__10_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__11_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__12_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__11_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__12_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__13_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 109, 105, 115, 115,
            105, 110, 103, 65, 114, 103, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__13_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__14_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__13_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__14_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__15_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__14_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__15_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__16_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 109, 105, 115, 115,
            105, 110, 103, 79, 112, 116, 65, 114, 103, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__16_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__17_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__16_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__17_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__18_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__17_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__18_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__19_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108,
            105, 100, 79, 112, 116, 65, 114, 103, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__19_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__20_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__19_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__20_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__21_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__20_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__21_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__22_value: LeanStringObject<33> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 83, 104, 111, 114, 116, 79, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__22_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__23_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__22_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__23_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__24_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__23_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__24_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__25_value: LeanStringObject<32> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 76, 111, 110, 103, 79, 112, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__25_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__26_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__25_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__26_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__27_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__26_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__27_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__28_value: LeanStringObject<34> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 101, 120,
            112, 101, 99, 116, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 115, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__28_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__29_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__28_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__29_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__30_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__29_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__30_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__31_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 84, 101, 109, 112, 108, 97, 116, 101, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__31_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__32_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__31_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__32_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__33_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__32_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__33_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__34_value: LeanStringObject<32> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 67, 111, 110, 102, 105, 103, 76, 97, 110, 103, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__34_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__35_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__34_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__35_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__36_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__35_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__36_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__37_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 77, 111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__37_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__38_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__37_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__38_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__39_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__38_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__39_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__40_value: LeanStringObject<32> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 77, 111, 100, 117, 108, 101, 80, 97, 116, 104, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__40_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__41_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__40_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__41_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__42_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__41_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__42_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__43_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [70, 105, 108, 101, 80, 97, 116, 104, 46, 109, 107, 32, 0],
    };
static mut l_Lake_instReprCliError_repr___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__43_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__44_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__43_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__44_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__45_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 80, 97, 99, 107, 97, 103, 101, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__45_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__46_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__45_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__46_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__47_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__46_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__47_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__48_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 70, 97, 99, 101, 116, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__48_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__49_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__48_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__49_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__50_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__49_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__50_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__51_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 84, 97, 114, 103, 101, 116, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__51_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__52_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__51_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__52_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__53_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__52_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__53_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__54_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 109, 105, 115, 115,
            105, 110, 103, 77, 111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__54_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__55_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__54_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__55_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__56_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__55_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__56_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__57_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 109, 105, 115, 115,
            105, 110, 103, 84, 97, 114, 103, 101, 116, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__57_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__58_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__57_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__58_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__59_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__58_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__59_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__60_value: LeanStringObject<33> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108,
            105, 100, 66, 117, 105, 108, 100, 84, 97, 114, 103, 101, 116, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__60: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__60_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__61_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__60_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__61_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__62_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__61_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__62_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__63_value: LeanStringObject<32> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108,
            105, 100, 84, 97, 114, 103, 101, 116, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__63_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__64_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__63_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__64_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__65_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__64_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__65_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__66_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108,
            105, 100, 70, 97, 99, 101, 116, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__66: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__66_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__67_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__66_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__67: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__67_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__68_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__67_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__68: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__68_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__69_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 69, 120, 101, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__69: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__69_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__70_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__69_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__70: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__70_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__71_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__70_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__71: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__71_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__72_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 117, 110, 107, 110,
            111, 119, 110, 83, 99, 114, 105, 112, 116, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__72: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__72_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__73_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__72_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__73: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__73_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__74_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__73_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__74: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__74_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__75_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 109, 105, 115, 115,
            105, 110, 103, 83, 99, 114, 105, 112, 116, 68, 111, 99, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__75: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__75_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__76_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__75_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__76: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__76_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__77_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__76_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__77: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__77_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__78_value: LeanStringObject<32> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108,
            105, 100, 83, 99, 114, 105, 112, 116, 83, 112, 101, 99, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__78: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__78_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__79_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__78_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__79: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__79_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__80_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__79_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__80: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__80_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__81_value: LeanStringObject<33> =
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
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 111, 117, 116, 112,
            117, 116, 67, 111, 110, 102, 105, 103, 69, 120, 105, 115, 116, 115, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__81: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__81_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__82_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__81_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__82: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__82_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__83_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__82_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__83: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__83_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__84_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 108, 101, 97, 110, 82,
            101, 118, 77, 105, 115, 109, 97, 116, 99, 104, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__84: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__84_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__85_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__84_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__85: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__85_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__86_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__85_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__86: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__86_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__87_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 105, 110, 118, 97, 108,
            105, 100, 69, 110, 118, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__87: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__87_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__88_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__87_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__88: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__88_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__89_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__88_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__89: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__89_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__90_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 97, 107, 101, 46, 67, 108, 105, 69, 114, 114, 111, 114, 46, 109, 105, 115, 115,
            105, 110, 103, 82, 111, 111, 116, 68, 105, 114, 0,
        ],
    };
static mut l_Lake_instReprCliError_repr___closed__90: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__90_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__91_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__90_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__91: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__91_value) as *mut LeanObject;
pub static l_Lake_instReprCliError_repr___closed__92_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__91_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprCliError_repr___closed__92: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError_repr___closed__92_value) as *mut LeanObject;
pub static l_Lake_instReprCliError___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprCliError_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprCliError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprCliError: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprCliError___closed__0_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__0_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        109, 105, 115, 115, 105, 110, 103, 32, 99, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__0_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__1_value: LeanStringObject<18> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 109, 109, 97, 110, 100, 32, 39, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__1_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__2_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [39, 0],
};
static mut l_Lake_CliError_toString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__2_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__3_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [109, 105, 115, 115, 105, 110, 103, 32, 0],
};
static mut l_Lake_CliError_toString___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__3_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__4_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [32, 102, 111, 114, 32, 0],
};
static mut l_Lake_CliError_toString___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__4_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__5_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 102, 111,
        114, 32, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__5_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__6_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [59, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 0],
};
static mut l_Lake_CliError_toString___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__6_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__7_value: LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 115, 104, 111, 114, 116, 32, 111, 112, 116, 105,
        111, 110, 32, 39, 45, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__7_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__8_value: LeanStringObject<1> = LeanStringObject {
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
static mut l_Lake_CliError_toString___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__8_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__9_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 108, 111, 110, 103, 32, 111, 112, 116, 105, 111,
        110, 32, 39, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__9_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__10_value: LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116,
        115, 58, 32, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__10_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__11_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [32, 0],
};
static mut l_Lake_CliError_toString___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__11_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__12_value: LeanStringObject<91> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 91,
    m_capacity: 91,
    m_length: 90,
    m_data: [
        116, 104, 101, 32, 96, 43, 96, 32, 111, 112, 116, 105, 111, 110, 32, 105, 115, 32, 97, 110,
        32, 69, 108, 97, 110, 32, 102, 101, 97, 116, 117, 114, 101, 59, 32, 114, 101, 114, 117,
        110, 32, 76, 97, 107, 101, 32, 118, 105, 97, 32, 69, 108, 97, 110, 32, 97, 110, 100, 32,
        101, 110, 115, 117, 114, 101, 32, 116, 104, 105, 115, 32, 111, 112, 116, 105, 111, 110, 32,
        99, 111, 109, 101, 115, 32, 102, 105, 114, 115, 116, 46, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__12_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__13_value: LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 116, 101, 109,
        112, 108, 97, 116, 101, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__13_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__14_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lake_CliError_toString___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__14_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__15_value: LeanStringObject<33> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105,
        111, 110, 32, 108, 97, 110, 103, 117, 97, 103, 101, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__15_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__16_value: LeanStringObject<17> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 109, 111, 100, 117, 108, 101, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__16_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__17_value: LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 109, 111, 100, 117, 108, 101, 32, 115, 111, 117,
        114, 99, 101, 32, 112, 97, 116, 104, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__17_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__18_value: LeanStringObject<18> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 112, 97, 99, 107, 97, 103, 101, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__18_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__19_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [117, 110, 107, 110, 111, 119, 110, 32, 0],
};
static mut l_Lake_CliError_toString___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__19_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__20_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [32, 102, 97, 99, 101, 116, 32, 96, 0],
};
static mut l_Lake_CliError_toString___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__20_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__21_value: LeanStringObject<17> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 116, 97, 114, 103, 101, 116, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__21_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__22_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [112, 97, 99, 107, 97, 103, 101, 32, 39, 0],
};
static mut l_Lake_CliError_toString___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__22_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__23_value: LeanStringObject<18> = LeanStringObject {
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
        39, 32, 104, 97, 115, 32, 110, 111, 32, 109, 111, 100, 117, 108, 101, 32, 39, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__23_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__24_value: LeanStringObject<18> = LeanStringObject {
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
        39, 32, 104, 97, 115, 32, 110, 111, 32, 116, 97, 114, 103, 101, 116, 32, 39, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__24_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__25_value: LeanStringObject<58> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        39, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 98, 117, 105, 108, 100, 32, 116, 97, 114,
        103, 101, 116, 32, 40, 112, 101, 114, 104, 97, 112, 115, 32, 121, 111, 117, 32, 109, 101,
        97, 110, 116, 32, 39, 108, 97, 107, 101, 32, 113, 117, 101, 114, 121, 39, 63, 41, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__25_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__26_value: LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 116, 97, 114, 103, 101, 116, 32, 115, 112, 101, 99,
        105, 102, 105, 101, 114, 32, 39, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__26_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__27_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [39, 32, 40, 116, 111, 111, 32, 109, 97, 110, 121, 32, 39, 0],
};
static mut l_Lake_CliError_toString___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__27_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__28_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [39, 41, 0],
};
static mut l_Lake_CliError_toString___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__28_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__29_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 102, 97, 99, 101, 116, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__29_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__30_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [96, 59, 32, 116, 97, 114, 103, 101, 116, 32, 0],
};
static mut l_Lake_CliError_toString___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__30_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__31_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        32, 104, 97, 115, 32, 110, 111, 32, 102, 97, 99, 101, 116, 115, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__31_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__32_value: LeanStringObject<20> = LeanStringObject {
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
        117, 110, 107, 110, 111, 119, 110, 32, 101, 120, 101, 99, 117, 116, 97, 98, 108, 101, 32, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__32_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__33_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        117, 110, 107, 110, 111, 119, 110, 32, 115, 99, 114, 105, 112, 116, 32, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__33_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__34_value: LeanStringObject<32> = LeanStringObject {
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
        110, 111, 32, 100, 111, 99, 117, 109, 101, 110, 116, 97, 116, 105, 111, 110, 32, 112, 114,
        111, 118, 105, 100, 101, 100, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__34_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__35_value: LeanStringObject<27> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 115, 99, 114, 105, 112, 116, 32, 115, 112, 101, 99,
        105, 102, 105, 101, 114, 32, 39, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__35_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__36_value: LeanStringObject<17> = LeanStringObject {
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
        39, 32, 40, 116, 111, 111, 32, 109, 97, 110, 121, 32, 39, 47, 39, 41, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__36_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__37_value: LeanStringObject<43> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        111, 117, 116, 112, 117, 116, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111,
        110, 32, 102, 105, 108, 101, 32, 97, 108, 114, 101, 97, 100, 121, 32, 101, 120, 105, 115,
        116, 115, 58, 32, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__37_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__38_value: LeanStringObject<37> = LeanStringObject {
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
        99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 116, 101, 99, 116, 32, 97, 32, 76,
        101, 97, 110, 32, 105, 110, 115, 116, 97, 108, 108, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__38_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__39_value: LeanStringObject<60> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 60,
    m_capacity: 60,
    m_length: 59,
    m_data: [
        99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 116, 101, 99, 116, 32, 116, 104,
        101, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 111, 102, 32,
        116, 104, 101, 32, 76, 97, 107, 101, 32, 105, 110, 115, 116, 97, 108, 108, 97, 116, 105,
        111, 110, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__39_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__40_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 76, 101, 97, 110, 32, 99, 111, 109, 109, 105,
        116, 32, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__40_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__41_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [44, 32, 98, 117, 116, 32, 103, 111, 116, 32, 0],
};
static mut l_Lake_CliError_toString___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__41_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__42_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 111, 116, 104, 105, 110, 103, 0],
};
static mut l_Lake_CliError_toString___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__42_value) as *mut LeanObject;
pub static l_Lake_CliError_toString___closed__43_value: LeanStringObject<32> = LeanStringObject {
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
        119, 111, 114, 107, 115, 112, 97, 99, 101, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121,
        32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58, 32, 0,
    ],
};
static mut l_Lake_CliError_toString___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_toString___closed__43_value) as *mut LeanObject;
pub static l_Lake_CliError_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_CliError_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_CliError_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_CliError_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_CliError_instToString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_CliError_ctorIdx(mut v_x_1492_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_1492_) {
        0 => {
            let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
            v___x_1493_ = lean_unsigned_to_nat(0);
            return v___x_1493_;
        }
        1 => {
            let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
            v___x_1494_ = lean_unsigned_to_nat(1);
            return v___x_1494_;
        }
        2 => {
            let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
            v___x_1495_ = lean_unsigned_to_nat(2);
            return v___x_1495_;
        }
        3 => {
            let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
            v___x_1496_ = lean_unsigned_to_nat(3);
            return v___x_1496_;
        }
        4 => {
            let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
            v___x_1497_ = lean_unsigned_to_nat(4);
            return v___x_1497_;
        }
        5 => {
            let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
            v___x_1498_ = lean_unsigned_to_nat(5);
            return v___x_1498_;
        }
        6 => {
            let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
            v___x_1499_ = lean_unsigned_to_nat(6);
            return v___x_1499_;
        }
        7 => {
            let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
            v___x_1500_ = lean_unsigned_to_nat(7);
            return v___x_1500_;
        }
        8 => {
            let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
            v___x_1501_ = lean_unsigned_to_nat(8);
            return v___x_1501_;
        }
        9 => {
            let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
            v___x_1502_ = lean_unsigned_to_nat(9);
            return v___x_1502_;
        }
        10 => {
            let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
            v___x_1503_ = lean_unsigned_to_nat(10);
            return v___x_1503_;
        }
        11 => {
            let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
            v___x_1504_ = lean_unsigned_to_nat(11);
            return v___x_1504_;
        }
        12 => {
            let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
            v___x_1505_ = lean_unsigned_to_nat(12);
            return v___x_1505_;
        }
        13 => {
            let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
            v___x_1506_ = lean_unsigned_to_nat(13);
            return v___x_1506_;
        }
        14 => {
            let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
            v___x_1507_ = lean_unsigned_to_nat(14);
            return v___x_1507_;
        }
        15 => {
            let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
            v___x_1508_ = lean_unsigned_to_nat(15);
            return v___x_1508_;
        }
        16 => {
            let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
            v___x_1509_ = lean_unsigned_to_nat(16);
            return v___x_1509_;
        }
        17 => {
            let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
            v___x_1510_ = lean_unsigned_to_nat(17);
            return v___x_1510_;
        }
        18 => {
            let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
            v___x_1511_ = lean_unsigned_to_nat(18);
            return v___x_1511_;
        }
        19 => {
            let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
            v___x_1512_ = lean_unsigned_to_nat(19);
            return v___x_1512_;
        }
        20 => {
            let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
            v___x_1513_ = lean_unsigned_to_nat(20);
            return v___x_1513_;
        }
        21 => {
            let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
            v___x_1514_ = lean_unsigned_to_nat(21);
            return v___x_1514_;
        }
        22 => {
            let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
            v___x_1515_ = lean_unsigned_to_nat(22);
            return v___x_1515_;
        }
        23 => {
            let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
            v___x_1516_ = lean_unsigned_to_nat(23);
            return v___x_1516_;
        }
        24 => {
            let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
            v___x_1517_ = lean_unsigned_to_nat(24);
            return v___x_1517_;
        }
        25 => {
            let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
            v___x_1518_ = lean_unsigned_to_nat(25);
            return v___x_1518_;
        }
        26 => {
            let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
            v___x_1519_ = lean_unsigned_to_nat(26);
            return v___x_1519_;
        }
        27 => {
            let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
            v___x_1520_ = lean_unsigned_to_nat(27);
            return v___x_1520_;
        }
        28 => {
            let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
            v___x_1521_ = lean_unsigned_to_nat(28);
            return v___x_1521_;
        }
        29 => {
            let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
            v___x_1522_ = lean_unsigned_to_nat(29);
            return v___x_1522_;
        }
        _ => {
            let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
            v___x_1523_ = lean_unsigned_to_nat(30);
            return v___x_1523_;
        }
    }
}
pub unsafe fn l_Lake_CliError_ctorIdx___boxed(mut v_x_1524_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Lake_CliError_ctorIdx(v_x_1524_);
    lean_dec(v_x_1524_);
    return v_res_1525_;
}
pub unsafe fn l_Lake_CliError_ctorElim___redArg(
    mut v_t_1526_: *mut LeanObject,
    mut v_k_1527_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1526_) {
        1 => {
            let mut v_cmd_1528_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
            v_cmd_1528_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_cmd_1528_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1529_ = lean_apply_1(v_k_1527_, v_cmd_1528_);
            return v___x_1529_;
        }
        2 => {
            let mut v_arg_1530_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
            v_arg_1530_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_arg_1530_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1531_ = lean_apply_1(v_k_1527_, v_arg_1530_);
            return v___x_1531_;
        }
        3 => {
            let mut v_opt_1532_: *mut LeanObject = core::ptr::null_mut();
            let mut v_arg_1533_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
            v_opt_1532_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_opt_1532_);
            v_arg_1533_ = lean_ctor_get(v_t_1526_, 1);
            lean_inc_ref(v_arg_1533_);
            lean_dec_ref_known(v_t_1526_, 2);
            v___x_1534_ = lean_apply_2(v_k_1527_, v_opt_1532_, v_arg_1533_);
            return v___x_1534_;
        }
        4 => {
            let mut v_opt_1535_: *mut LeanObject = core::ptr::null_mut();
            let mut v_arg_1536_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
            v_opt_1535_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_opt_1535_);
            v_arg_1536_ = lean_ctor_get(v_t_1526_, 1);
            lean_inc_ref(v_arg_1536_);
            lean_dec_ref_known(v_t_1526_, 2);
            v___x_1537_ = lean_apply_2(v_k_1527_, v_opt_1535_, v_arg_1536_);
            return v___x_1537_;
        }
        5 => {
            let mut v_opt_1538_: u32 = 0;
            let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
            v_opt_1538_ = lean_ctor_get_uint32(v_t_1526_, 0 as u32);
            lean_dec_ref_known(v_t_1526_, 0);
            v___x_1539_ = lean_box_uint32(v_opt_1538_);
            v___x_1540_ = lean_apply_1(v_k_1527_, v___x_1539_);
            return v___x_1540_;
        }
        6 => {
            let mut v_opt_1541_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
            v_opt_1541_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_opt_1541_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1542_ = lean_apply_1(v_k_1527_, v_opt_1541_);
            return v___x_1542_;
        }
        7 => {
            let mut v_args_1543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
            v_args_1543_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc(v_args_1543_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1544_ = lean_apply_1(v_k_1527_, v_args_1543_);
            return v___x_1544_;
        }
        9 => {
            let mut v_spec_1545_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
            v_spec_1545_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_spec_1545_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1546_ = lean_apply_1(v_k_1527_, v_spec_1545_);
            return v___x_1546_;
        }
        10 => {
            let mut v_spec_1547_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
            v_spec_1547_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_spec_1547_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1548_ = lean_apply_1(v_k_1527_, v_spec_1547_);
            return v___x_1548_;
        }
        11 => {
            let mut v_mod_1549_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
            v_mod_1549_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc(v_mod_1549_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1550_ = lean_apply_1(v_k_1527_, v_mod_1549_);
            return v___x_1550_;
        }
        12 => {
            let mut v_path_1551_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
            v_path_1551_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_path_1551_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1552_ = lean_apply_1(v_k_1527_, v_path_1551_);
            return v___x_1552_;
        }
        13 => {
            let mut v_spec_1553_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
            v_spec_1553_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_spec_1553_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1554_ = lean_apply_1(v_k_1527_, v_spec_1553_);
            return v___x_1554_;
        }
        14 => {
            let mut v_type_1555_: *mut LeanObject = core::ptr::null_mut();
            let mut v_facet_1556_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
            v_type_1555_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_type_1555_);
            v_facet_1556_ = lean_ctor_get(v_t_1526_, 1);
            lean_inc(v_facet_1556_);
            lean_dec_ref_known(v_t_1526_, 2);
            v___x_1557_ = lean_apply_2(v_k_1527_, v_type_1555_, v_facet_1556_);
            return v___x_1557_;
        }
        15 => {
            let mut v_target_1558_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
            v_target_1558_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc(v_target_1558_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1559_ = lean_apply_1(v_k_1527_, v_target_1558_);
            return v___x_1559_;
        }
        16 => {
            let mut v_pkg_1560_: *mut LeanObject = core::ptr::null_mut();
            let mut v_mod_1561_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
            v_pkg_1560_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc(v_pkg_1560_);
            v_mod_1561_ = lean_ctor_get(v_t_1526_, 1);
            lean_inc(v_mod_1561_);
            lean_dec_ref_known(v_t_1526_, 2);
            v___x_1562_ = lean_apply_2(v_k_1527_, v_pkg_1560_, v_mod_1561_);
            return v___x_1562_;
        }
        17 => {
            let mut v_pkg_1563_: *mut LeanObject = core::ptr::null_mut();
            let mut v_spec_1564_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
            v_pkg_1563_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc(v_pkg_1563_);
            v_spec_1564_ = lean_ctor_get(v_t_1526_, 1);
            lean_inc_ref(v_spec_1564_);
            lean_dec_ref_known(v_t_1526_, 2);
            v___x_1565_ = lean_apply_2(v_k_1527_, v_pkg_1563_, v_spec_1564_);
            return v___x_1565_;
        }
        18 => {
            let mut v_key_1566_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
            v_key_1566_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_key_1566_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1567_ = lean_apply_1(v_k_1527_, v_key_1566_);
            return v___x_1567_;
        }
        19 => {
            let mut v_spec_1568_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tooMany_1569_: u32 = 0;
            let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
            v_spec_1568_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_spec_1568_);
            v_tooMany_1569_ = lean_ctor_get_uint32(
                v_t_1526_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1570_ = lean_box_uint32(v_tooMany_1569_);
            v___x_1571_ = lean_apply_2(v_k_1527_, v_spec_1568_, v___x_1570_);
            return v___x_1571_;
        }
        20 => {
            let mut v_target_1572_: *mut LeanObject = core::ptr::null_mut();
            let mut v_facet_1573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
            v_target_1572_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc(v_target_1572_);
            v_facet_1573_ = lean_ctor_get(v_t_1526_, 1);
            lean_inc(v_facet_1573_);
            lean_dec_ref_known(v_t_1526_, 2);
            v___x_1574_ = lean_apply_2(v_k_1527_, v_target_1572_, v_facet_1573_);
            return v___x_1574_;
        }
        21 => {
            let mut v_spec_1575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
            v_spec_1575_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_spec_1575_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1576_ = lean_apply_1(v_k_1527_, v_spec_1575_);
            return v___x_1576_;
        }
        22 => {
            let mut v_script_1577_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
            v_script_1577_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_script_1577_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1578_ = lean_apply_1(v_k_1527_, v_script_1577_);
            return v___x_1578_;
        }
        23 => {
            let mut v_script_1579_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
            v_script_1579_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_script_1579_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1580_ = lean_apply_1(v_k_1527_, v_script_1579_);
            return v___x_1580_;
        }
        24 => {
            let mut v_spec_1581_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
            v_spec_1581_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_spec_1581_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1582_ = lean_apply_1(v_k_1527_, v_spec_1581_);
            return v___x_1582_;
        }
        25 => {
            let mut v_path_1583_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
            v_path_1583_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_path_1583_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1584_ = lean_apply_1(v_k_1527_, v_path_1583_);
            return v___x_1584_;
        }
        28 => {
            let mut v_expected_1585_: *mut LeanObject = core::ptr::null_mut();
            let mut v_actual_1586_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
            v_expected_1585_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_expected_1585_);
            v_actual_1586_ = lean_ctor_get(v_t_1526_, 1);
            lean_inc_ref(v_actual_1586_);
            lean_dec_ref_known(v_t_1526_, 2);
            v___x_1587_ = lean_apply_2(v_k_1527_, v_expected_1585_, v_actual_1586_);
            return v___x_1587_;
        }
        29 => {
            let mut v_msg_1588_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
            v_msg_1588_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_msg_1588_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1589_ = lean_apply_1(v_k_1527_, v_msg_1588_);
            return v___x_1589_;
        }
        30 => {
            let mut v_path_1590_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
            v_path_1590_ = lean_ctor_get(v_t_1526_, 0);
            lean_inc_ref(v_path_1590_);
            lean_dec_ref_known(v_t_1526_, 1);
            v___x_1591_ = lean_apply_1(v_k_1527_, v_path_1590_);
            return v___x_1591_;
        }
        _ => {
            lean_dec(v_t_1526_);
            return v_k_1527_;
        }
    }
}
pub unsafe fn l_Lake_CliError_ctorElim(
    mut v_motive_1592_: *mut LeanObject,
    mut v_ctorIdx_1593_: *mut LeanObject,
    mut v_t_1594_: *mut LeanObject,
    mut v_h_1595_: *mut LeanObject,
    mut v_k_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lake_CliError_ctorElim___redArg(v_t_1594_, v_k_1596_);
    return v___x_1597_;
}
pub unsafe fn l_Lake_CliError_ctorElim___boxed(
    mut v_motive_1598_: *mut LeanObject,
    mut v_ctorIdx_1599_: *mut LeanObject,
    mut v_t_1600_: *mut LeanObject,
    mut v_h_1601_: *mut LeanObject,
    mut v_k_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1603_: *mut LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lake_CliError_ctorElim(
        v_motive_1598_,
        v_ctorIdx_1599_,
        v_t_1600_,
        v_h_1601_,
        v_k_1602_,
    );
    lean_dec(v_ctorIdx_1599_);
    return v_res_1603_;
}
pub unsafe fn l_Lake_CliError_missingCommand_elim___redArg(
    mut v_t_1604_: *mut LeanObject,
    mut v_missingCommand_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lake_CliError_ctorElim___redArg(v_t_1604_, v_missingCommand_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Lake_CliError_missingCommand_elim(
    mut v_motive_1607_: *mut LeanObject,
    mut v_t_1608_: *mut LeanObject,
    mut v_h_1609_: *mut LeanObject,
    mut v_missingCommand_1610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    v___x_1611_ = l_Lake_CliError_ctorElim___redArg(v_t_1608_, v_missingCommand_1610_);
    return v___x_1611_;
}
pub unsafe fn l_Lake_CliError_unknownCommand_elim___redArg(
    mut v_t_1612_: *mut LeanObject,
    mut v_unknownCommand_1613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = l_Lake_CliError_ctorElim___redArg(v_t_1612_, v_unknownCommand_1613_);
    return v___x_1614_;
}
pub unsafe fn l_Lake_CliError_unknownCommand_elim(
    mut v_motive_1615_: *mut LeanObject,
    mut v_t_1616_: *mut LeanObject,
    mut v_h_1617_: *mut LeanObject,
    mut v_unknownCommand_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    v___x_1619_ = l_Lake_CliError_ctorElim___redArg(v_t_1616_, v_unknownCommand_1618_);
    return v___x_1619_;
}
pub unsafe fn l_Lake_CliError_missingArg_elim___redArg(
    mut v_t_1620_: *mut LeanObject,
    mut v_missingArg_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lake_CliError_ctorElim___redArg(v_t_1620_, v_missingArg_1621_);
    return v___x_1622_;
}
pub unsafe fn l_Lake_CliError_missingArg_elim(
    mut v_motive_1623_: *mut LeanObject,
    mut v_t_1624_: *mut LeanObject,
    mut v_h_1625_: *mut LeanObject,
    mut v_missingArg_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lake_CliError_ctorElim___redArg(v_t_1624_, v_missingArg_1626_);
    return v___x_1627_;
}
pub unsafe fn l_Lake_CliError_missingOptArg_elim___redArg(
    mut v_t_1628_: *mut LeanObject,
    mut v_missingOptArg_1629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    v___x_1630_ = l_Lake_CliError_ctorElim___redArg(v_t_1628_, v_missingOptArg_1629_);
    return v___x_1630_;
}
pub unsafe fn l_Lake_CliError_missingOptArg_elim(
    mut v_motive_1631_: *mut LeanObject,
    mut v_t_1632_: *mut LeanObject,
    mut v_h_1633_: *mut LeanObject,
    mut v_missingOptArg_1634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_Lake_CliError_ctorElim___redArg(v_t_1632_, v_missingOptArg_1634_);
    return v___x_1635_;
}
pub unsafe fn l_Lake_CliError_invalidOptArg_elim___redArg(
    mut v_t_1636_: *mut LeanObject,
    mut v_invalidOptArg_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lake_CliError_ctorElim___redArg(v_t_1636_, v_invalidOptArg_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Lake_CliError_invalidOptArg_elim(
    mut v_motive_1639_: *mut LeanObject,
    mut v_t_1640_: *mut LeanObject,
    mut v_h_1641_: *mut LeanObject,
    mut v_invalidOptArg_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    v___x_1643_ = l_Lake_CliError_ctorElim___redArg(v_t_1640_, v_invalidOptArg_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Lake_CliError_unknownShortOption_elim___redArg(
    mut v_t_1644_: *mut LeanObject,
    mut v_unknownShortOption_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    v___x_1646_ = l_Lake_CliError_ctorElim___redArg(v_t_1644_, v_unknownShortOption_1645_);
    return v___x_1646_;
}
pub unsafe fn l_Lake_CliError_unknownShortOption_elim(
    mut v_motive_1647_: *mut LeanObject,
    mut v_t_1648_: *mut LeanObject,
    mut v_h_1649_: *mut LeanObject,
    mut v_unknownShortOption_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lake_CliError_ctorElim___redArg(v_t_1648_, v_unknownShortOption_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Lake_CliError_unknownLongOption_elim___redArg(
    mut v_t_1652_: *mut LeanObject,
    mut v_unknownLongOption_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    v___x_1654_ = l_Lake_CliError_ctorElim___redArg(v_t_1652_, v_unknownLongOption_1653_);
    return v___x_1654_;
}
pub unsafe fn l_Lake_CliError_unknownLongOption_elim(
    mut v_motive_1655_: *mut LeanObject,
    mut v_t_1656_: *mut LeanObject,
    mut v_h_1657_: *mut LeanObject,
    mut v_unknownLongOption_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Lake_CliError_ctorElim___redArg(v_t_1656_, v_unknownLongOption_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Lake_CliError_unexpectedArguments_elim___redArg(
    mut v_t_1660_: *mut LeanObject,
    mut v_unexpectedArguments_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1662_ = l_Lake_CliError_ctorElim___redArg(v_t_1660_, v_unexpectedArguments_1661_);
    return v___x_1662_;
}
pub unsafe fn l_Lake_CliError_unexpectedArguments_elim(
    mut v_motive_1663_: *mut LeanObject,
    mut v_t_1664_: *mut LeanObject,
    mut v_h_1665_: *mut LeanObject,
    mut v_unexpectedArguments_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1667_ = l_Lake_CliError_ctorElim___redArg(v_t_1664_, v_unexpectedArguments_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lake_CliError_unexpectedPlus_elim___redArg(
    mut v_t_1668_: *mut LeanObject,
    mut v_unexpectedPlus_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    v___x_1670_ = l_Lake_CliError_ctorElim___redArg(v_t_1668_, v_unexpectedPlus_1669_);
    return v___x_1670_;
}
pub unsafe fn l_Lake_CliError_unexpectedPlus_elim(
    mut v_motive_1671_: *mut LeanObject,
    mut v_t_1672_: *mut LeanObject,
    mut v_h_1673_: *mut LeanObject,
    mut v_unexpectedPlus_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    v___x_1675_ = l_Lake_CliError_ctorElim___redArg(v_t_1672_, v_unexpectedPlus_1674_);
    return v___x_1675_;
}
pub unsafe fn l_Lake_CliError_unknownTemplate_elim___redArg(
    mut v_t_1676_: *mut LeanObject,
    mut v_unknownTemplate_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Lake_CliError_ctorElim___redArg(v_t_1676_, v_unknownTemplate_1677_);
    return v___x_1678_;
}
pub unsafe fn l_Lake_CliError_unknownTemplate_elim(
    mut v_motive_1679_: *mut LeanObject,
    mut v_t_1680_: *mut LeanObject,
    mut v_h_1681_: *mut LeanObject,
    mut v_unknownTemplate_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = l_Lake_CliError_ctorElim___redArg(v_t_1680_, v_unknownTemplate_1682_);
    return v___x_1683_;
}
pub unsafe fn l_Lake_CliError_unknownConfigLang_elim___redArg(
    mut v_t_1684_: *mut LeanObject,
    mut v_unknownConfigLang_1685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    v___x_1686_ = l_Lake_CliError_ctorElim___redArg(v_t_1684_, v_unknownConfigLang_1685_);
    return v___x_1686_;
}
pub unsafe fn l_Lake_CliError_unknownConfigLang_elim(
    mut v_motive_1687_: *mut LeanObject,
    mut v_t_1688_: *mut LeanObject,
    mut v_h_1689_: *mut LeanObject,
    mut v_unknownConfigLang_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lake_CliError_ctorElim___redArg(v_t_1688_, v_unknownConfigLang_1690_);
    return v___x_1691_;
}
pub unsafe fn l_Lake_CliError_unknownModule_elim___redArg(
    mut v_t_1692_: *mut LeanObject,
    mut v_unknownModule_1693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_Lake_CliError_ctorElim___redArg(v_t_1692_, v_unknownModule_1693_);
    return v___x_1694_;
}
pub unsafe fn l_Lake_CliError_unknownModule_elim(
    mut v_motive_1695_: *mut LeanObject,
    mut v_t_1696_: *mut LeanObject,
    mut v_h_1697_: *mut LeanObject,
    mut v_unknownModule_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lake_CliError_ctorElim___redArg(v_t_1696_, v_unknownModule_1698_);
    return v___x_1699_;
}
pub unsafe fn l_Lake_CliError_unknownModulePath_elim___redArg(
    mut v_t_1700_: *mut LeanObject,
    mut v_unknownModulePath_1701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    v___x_1702_ = l_Lake_CliError_ctorElim___redArg(v_t_1700_, v_unknownModulePath_1701_);
    return v___x_1702_;
}
pub unsafe fn l_Lake_CliError_unknownModulePath_elim(
    mut v_motive_1703_: *mut LeanObject,
    mut v_t_1704_: *mut LeanObject,
    mut v_h_1705_: *mut LeanObject,
    mut v_unknownModulePath_1706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    v___x_1707_ = l_Lake_CliError_ctorElim___redArg(v_t_1704_, v_unknownModulePath_1706_);
    return v___x_1707_;
}
pub unsafe fn l_Lake_CliError_unknownPackage_elim___redArg(
    mut v_t_1708_: *mut LeanObject,
    mut v_unknownPackage_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    v___x_1710_ = l_Lake_CliError_ctorElim___redArg(v_t_1708_, v_unknownPackage_1709_);
    return v___x_1710_;
}
pub unsafe fn l_Lake_CliError_unknownPackage_elim(
    mut v_motive_1711_: *mut LeanObject,
    mut v_t_1712_: *mut LeanObject,
    mut v_h_1713_: *mut LeanObject,
    mut v_unknownPackage_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_Lake_CliError_ctorElim___redArg(v_t_1712_, v_unknownPackage_1714_);
    return v___x_1715_;
}
pub unsafe fn l_Lake_CliError_unknownFacet_elim___redArg(
    mut v_t_1716_: *mut LeanObject,
    mut v_unknownFacet_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    v___x_1718_ = l_Lake_CliError_ctorElim___redArg(v_t_1716_, v_unknownFacet_1717_);
    return v___x_1718_;
}
pub unsafe fn l_Lake_CliError_unknownFacet_elim(
    mut v_motive_1719_: *mut LeanObject,
    mut v_t_1720_: *mut LeanObject,
    mut v_h_1721_: *mut LeanObject,
    mut v_unknownFacet_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_Lake_CliError_ctorElim___redArg(v_t_1720_, v_unknownFacet_1722_);
    return v___x_1723_;
}
pub unsafe fn l_Lake_CliError_unknownTarget_elim___redArg(
    mut v_t_1724_: *mut LeanObject,
    mut v_unknownTarget_1725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    v___x_1726_ = l_Lake_CliError_ctorElim___redArg(v_t_1724_, v_unknownTarget_1725_);
    return v___x_1726_;
}
pub unsafe fn l_Lake_CliError_unknownTarget_elim(
    mut v_motive_1727_: *mut LeanObject,
    mut v_t_1728_: *mut LeanObject,
    mut v_h_1729_: *mut LeanObject,
    mut v_unknownTarget_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    v___x_1731_ = l_Lake_CliError_ctorElim___redArg(v_t_1728_, v_unknownTarget_1730_);
    return v___x_1731_;
}
pub unsafe fn l_Lake_CliError_missingModule_elim___redArg(
    mut v_t_1732_: *mut LeanObject,
    mut v_missingModule_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = l_Lake_CliError_ctorElim___redArg(v_t_1732_, v_missingModule_1733_);
    return v___x_1734_;
}
pub unsafe fn l_Lake_CliError_missingModule_elim(
    mut v_motive_1735_: *mut LeanObject,
    mut v_t_1736_: *mut LeanObject,
    mut v_h_1737_: *mut LeanObject,
    mut v_missingModule_1738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    v___x_1739_ = l_Lake_CliError_ctorElim___redArg(v_t_1736_, v_missingModule_1738_);
    return v___x_1739_;
}
pub unsafe fn l_Lake_CliError_missingTarget_elim___redArg(
    mut v_t_1740_: *mut LeanObject,
    mut v_missingTarget_1741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    v___x_1742_ = l_Lake_CliError_ctorElim___redArg(v_t_1740_, v_missingTarget_1741_);
    return v___x_1742_;
}
pub unsafe fn l_Lake_CliError_missingTarget_elim(
    mut v_motive_1743_: *mut LeanObject,
    mut v_t_1744_: *mut LeanObject,
    mut v_h_1745_: *mut LeanObject,
    mut v_missingTarget_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lake_CliError_ctorElim___redArg(v_t_1744_, v_missingTarget_1746_);
    return v___x_1747_;
}
pub unsafe fn l_Lake_CliError_invalidBuildTarget_elim___redArg(
    mut v_t_1748_: *mut LeanObject,
    mut v_invalidBuildTarget_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    v___x_1750_ = l_Lake_CliError_ctorElim___redArg(v_t_1748_, v_invalidBuildTarget_1749_);
    return v___x_1750_;
}
pub unsafe fn l_Lake_CliError_invalidBuildTarget_elim(
    mut v_motive_1751_: *mut LeanObject,
    mut v_t_1752_: *mut LeanObject,
    mut v_h_1753_: *mut LeanObject,
    mut v_invalidBuildTarget_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Lake_CliError_ctorElim___redArg(v_t_1752_, v_invalidBuildTarget_1754_);
    return v___x_1755_;
}
pub unsafe fn l_Lake_CliError_invalidTargetSpec_elim___redArg(
    mut v_t_1756_: *mut LeanObject,
    mut v_invalidTargetSpec_1757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    v___x_1758_ = l_Lake_CliError_ctorElim___redArg(v_t_1756_, v_invalidTargetSpec_1757_);
    return v___x_1758_;
}
pub unsafe fn l_Lake_CliError_invalidTargetSpec_elim(
    mut v_motive_1759_: *mut LeanObject,
    mut v_t_1760_: *mut LeanObject,
    mut v_h_1761_: *mut LeanObject,
    mut v_invalidTargetSpec_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_Lake_CliError_ctorElim___redArg(v_t_1760_, v_invalidTargetSpec_1762_);
    return v___x_1763_;
}
pub unsafe fn l_Lake_CliError_invalidFacet_elim___redArg(
    mut v_t_1764_: *mut LeanObject,
    mut v_invalidFacet_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    v___x_1766_ = l_Lake_CliError_ctorElim___redArg(v_t_1764_, v_invalidFacet_1765_);
    return v___x_1766_;
}
pub unsafe fn l_Lake_CliError_invalidFacet_elim(
    mut v_motive_1767_: *mut LeanObject,
    mut v_t_1768_: *mut LeanObject,
    mut v_h_1769_: *mut LeanObject,
    mut v_invalidFacet_1770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    v___x_1771_ = l_Lake_CliError_ctorElim___redArg(v_t_1768_, v_invalidFacet_1770_);
    return v___x_1771_;
}
pub unsafe fn l_Lake_CliError_unknownExe_elim___redArg(
    mut v_t_1772_: *mut LeanObject,
    mut v_unknownExe_1773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    v___x_1774_ = l_Lake_CliError_ctorElim___redArg(v_t_1772_, v_unknownExe_1773_);
    return v___x_1774_;
}
pub unsafe fn l_Lake_CliError_unknownExe_elim(
    mut v_motive_1775_: *mut LeanObject,
    mut v_t_1776_: *mut LeanObject,
    mut v_h_1777_: *mut LeanObject,
    mut v_unknownExe_1778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    v___x_1779_ = l_Lake_CliError_ctorElim___redArg(v_t_1776_, v_unknownExe_1778_);
    return v___x_1779_;
}
pub unsafe fn l_Lake_CliError_unknownScript_elim___redArg(
    mut v_t_1780_: *mut LeanObject,
    mut v_unknownScript_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    v___x_1782_ = l_Lake_CliError_ctorElim___redArg(v_t_1780_, v_unknownScript_1781_);
    return v___x_1782_;
}
pub unsafe fn l_Lake_CliError_unknownScript_elim(
    mut v_motive_1783_: *mut LeanObject,
    mut v_t_1784_: *mut LeanObject,
    mut v_h_1785_: *mut LeanObject,
    mut v_unknownScript_1786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    v___x_1787_ = l_Lake_CliError_ctorElim___redArg(v_t_1784_, v_unknownScript_1786_);
    return v___x_1787_;
}
pub unsafe fn l_Lake_CliError_missingScriptDoc_elim___redArg(
    mut v_t_1788_: *mut LeanObject,
    mut v_missingScriptDoc_1789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    v___x_1790_ = l_Lake_CliError_ctorElim___redArg(v_t_1788_, v_missingScriptDoc_1789_);
    return v___x_1790_;
}
pub unsafe fn l_Lake_CliError_missingScriptDoc_elim(
    mut v_motive_1791_: *mut LeanObject,
    mut v_t_1792_: *mut LeanObject,
    mut v_h_1793_: *mut LeanObject,
    mut v_missingScriptDoc_1794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lake_CliError_ctorElim___redArg(v_t_1792_, v_missingScriptDoc_1794_);
    return v___x_1795_;
}
pub unsafe fn l_Lake_CliError_invalidScriptSpec_elim___redArg(
    mut v_t_1796_: *mut LeanObject,
    mut v_invalidScriptSpec_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    v___x_1798_ = l_Lake_CliError_ctorElim___redArg(v_t_1796_, v_invalidScriptSpec_1797_);
    return v___x_1798_;
}
pub unsafe fn l_Lake_CliError_invalidScriptSpec_elim(
    mut v_motive_1799_: *mut LeanObject,
    mut v_t_1800_: *mut LeanObject,
    mut v_h_1801_: *mut LeanObject,
    mut v_invalidScriptSpec_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    v___x_1803_ = l_Lake_CliError_ctorElim___redArg(v_t_1800_, v_invalidScriptSpec_1802_);
    return v___x_1803_;
}
pub unsafe fn l_Lake_CliError_outputConfigExists_elim___redArg(
    mut v_t_1804_: *mut LeanObject,
    mut v_outputConfigExists_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    v___x_1806_ = l_Lake_CliError_ctorElim___redArg(v_t_1804_, v_outputConfigExists_1805_);
    return v___x_1806_;
}
pub unsafe fn l_Lake_CliError_outputConfigExists_elim(
    mut v_motive_1807_: *mut LeanObject,
    mut v_t_1808_: *mut LeanObject,
    mut v_h_1809_: *mut LeanObject,
    mut v_outputConfigExists_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    v___x_1811_ = l_Lake_CliError_ctorElim___redArg(v_t_1808_, v_outputConfigExists_1810_);
    return v___x_1811_;
}
pub unsafe fn l_Lake_CliError_unknownLeanInstall_elim___redArg(
    mut v_t_1812_: *mut LeanObject,
    mut v_unknownLeanInstall_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    v___x_1814_ = l_Lake_CliError_ctorElim___redArg(v_t_1812_, v_unknownLeanInstall_1813_);
    return v___x_1814_;
}
pub unsafe fn l_Lake_CliError_unknownLeanInstall_elim(
    mut v_motive_1815_: *mut LeanObject,
    mut v_t_1816_: *mut LeanObject,
    mut v_h_1817_: *mut LeanObject,
    mut v_unknownLeanInstall_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    v___x_1819_ = l_Lake_CliError_ctorElim___redArg(v_t_1816_, v_unknownLeanInstall_1818_);
    return v___x_1819_;
}
pub unsafe fn l_Lake_CliError_unknownLakeInstall_elim___redArg(
    mut v_t_1820_: *mut LeanObject,
    mut v_unknownLakeInstall_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = l_Lake_CliError_ctorElim___redArg(v_t_1820_, v_unknownLakeInstall_1821_);
    return v___x_1822_;
}
pub unsafe fn l_Lake_CliError_unknownLakeInstall_elim(
    mut v_motive_1823_: *mut LeanObject,
    mut v_t_1824_: *mut LeanObject,
    mut v_h_1825_: *mut LeanObject,
    mut v_unknownLakeInstall_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Lake_CliError_ctorElim___redArg(v_t_1824_, v_unknownLakeInstall_1826_);
    return v___x_1827_;
}
pub unsafe fn l_Lake_CliError_leanRevMismatch_elim___redArg(
    mut v_t_1828_: *mut LeanObject,
    mut v_leanRevMismatch_1829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_Lake_CliError_ctorElim___redArg(v_t_1828_, v_leanRevMismatch_1829_);
    return v___x_1830_;
}
pub unsafe fn l_Lake_CliError_leanRevMismatch_elim(
    mut v_motive_1831_: *mut LeanObject,
    mut v_t_1832_: *mut LeanObject,
    mut v_h_1833_: *mut LeanObject,
    mut v_leanRevMismatch_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lake_CliError_ctorElim___redArg(v_t_1832_, v_leanRevMismatch_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lake_CliError_invalidEnv_elim___redArg(
    mut v_t_1836_: *mut LeanObject,
    mut v_invalidEnv_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lake_CliError_ctorElim___redArg(v_t_1836_, v_invalidEnv_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Lake_CliError_invalidEnv_elim(
    mut v_motive_1839_: *mut LeanObject,
    mut v_t_1840_: *mut LeanObject,
    mut v_h_1841_: *mut LeanObject,
    mut v_invalidEnv_1842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Lake_CliError_ctorElim___redArg(v_t_1840_, v_invalidEnv_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Lake_CliError_missingRootDir_elim___redArg(
    mut v_t_1844_: *mut LeanObject,
    mut v_missingRootDir_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Lake_CliError_ctorElim___redArg(v_t_1844_, v_missingRootDir_1845_);
    return v___x_1846_;
}
pub unsafe fn l_Lake_CliError_missingRootDir_elim(
    mut v_motive_1847_: *mut LeanObject,
    mut v_t_1848_: *mut LeanObject,
    mut v_h_1849_: *mut LeanObject,
    mut v_missingRootDir_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ = l_Lake_CliError_ctorElim___redArg(v_t_1848_, v_missingRootDir_1850_);
    return v___x_1851_;
}
pub unsafe fn _init_l_Lake_instInhabitedCliError_default() -> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = lean_box(0);
    return v___x_1852_;
}
pub unsafe fn _init_l_Lake_instInhabitedCliError() -> *mut LeanObject {
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    v___x_1853_ = lean_box(0);
    return v___x_1853_;
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(
    mut v___y_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    v___x_1855_ = l_String_quote(v___y_1854_);
    v___x_1856_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1856_, 0, v___x_1855_);
    return v___x_1856_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(
    mut v_x_1857_: *mut LeanObject,
    mut v_x_1858_: *mut LeanObject,
    mut v_x_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1859_) == 0 {
                    lean_dec(v_x_1857_);
                    return v_x_1858_;
                } else {
                    v_head_1860_ = lean_ctor_get(v_x_1859_, 0);
                    v_tail_1861_ = lean_ctor_get(v_x_1859_, 1);
                    v_isSharedCheck_1872_ = (!lean_is_exclusive(v_x_1859_)) as u8;
                    if v_isSharedCheck_1872_ == 0 {
                        v___x_1863_ = v_x_1859_;
                        v_isShared_1864_ = v_isSharedCheck_1872_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1861_);
                        lean_inc(v_head_1860_);
                        lean_dec(v_x_1859_);
                        v___x_1863_ = lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1872_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1857_);
                if v_isShared_1864_ == 0 {
                    lean_ctor_set_tag(v___x_1863_, 5);
                    lean_ctor_set(v___x_1863_, 1, v_x_1857_);
                    lean_ctor_set(v___x_1863_, 0, v_x_1858_);
                    v___x_1866_ = v___x_1863_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_x_1858_);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_x_1857_);
                    v___x_1866_ = v_reuseFailAlloc_1871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1867_ = l_String_quote(v_head_1860_);
                v___x_1868_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1868_, 0, v___x_1867_);
                v___x_1869_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1869_, 0, v___x_1866_);
                lean_ctor_set(v___x_1869_, 1, v___x_1868_);
                v_x_1858_ = v___x_1869_;
                v_x_1859_ = v_tail_1861_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(
    mut v_x_1873_: *mut LeanObject,
    mut v_x_1874_: *mut LeanObject,
    mut v_x_1875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1875_) == 0 {
                    lean_dec(v_x_1873_);
                    return v_x_1874_;
                } else {
                    v_head_1876_ = lean_ctor_get(v_x_1875_, 0);
                    v_tail_1877_ = lean_ctor_get(v_x_1875_, 1);
                    v_isSharedCheck_1888_ = (!lean_is_exclusive(v_x_1875_)) as u8;
                    if v_isSharedCheck_1888_ == 0 {
                        v___x_1879_ = v_x_1875_;
                        v_isShared_1880_ = v_isSharedCheck_1888_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1877_);
                        lean_inc(v_head_1876_);
                        lean_dec(v_x_1875_);
                        v___x_1879_ = lean_box(0);
                        v_isShared_1880_ = v_isSharedCheck_1888_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1873_);
                if v_isShared_1880_ == 0 {
                    lean_ctor_set_tag(v___x_1879_, 5);
                    lean_ctor_set(v___x_1879_, 1, v_x_1873_);
                    lean_ctor_set(v___x_1879_, 0, v_x_1874_);
                    v___x_1882_ = v___x_1879_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1887_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_x_1874_);
                    lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_x_1873_);
                    v___x_1882_ = v_reuseFailAlloc_1887_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1883_ = l_String_quote(v_head_1876_);
                v___x_1884_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1884_, 0, v___x_1883_);
                v___x_1885_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1885_, 0, v___x_1882_);
                lean_ctor_set(v___x_1885_, 1, v___x_1884_);
                v___x_1886_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1_spec__3(v_x_1873_, v___x_1885_, v_tail_1877_);
                return v___x_1886_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(
    mut v_x_1889_: *mut LeanObject,
    mut v_x_1890_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1889_) == 0 {
        let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1890_);
        v___x_1891_ = lean_box(0);
        return v___x_1891_;
    } else {
        let mut v_tail_1892_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1892_ = lean_ctor_get(v_x_1889_, 1);
        if lean_obj_tag(v_tail_1892_) == 0 {
            let mut v_head_1893_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_1890_);
            v_head_1893_ = lean_ctor_get(v_x_1889_, 0);
            lean_inc(v_head_1893_);
            lean_dec_ref_known(v_x_1889_, 2);
            v___x_1894_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(v_head_1893_);
            return v___x_1894_;
        } else {
            let mut v_head_1895_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_1892_);
            v_head_1895_ = lean_ctor_get(v_x_1889_, 0);
            lean_inc(v_head_1895_);
            lean_dec_ref_known(v_x_1889_, 2);
            v___x_1896_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0___lam__0(v_head_1895_);
            v___x_1897_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0_spec__1(v_x_1890_, v___x_1896_, v_tail_1892_);
            return v___x_1897_;
        }
    }
}
pub unsafe fn _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    v___x_1909_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__2;
    v___x_1910_ = lean_string_length(v___x_1909_);
    return v___x_1910_;
}
pub unsafe fn _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    v___x_1911_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7_once
        ),
        _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__7,
    );
    v___x_1912_ = lean_nat_to_int(v___x_1911_);
    return v___x_1912_;
}
pub unsafe fn l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(
    mut v_a_1917_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_1917_) == 0 {
        let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
        v___x_1918_ =
            l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__1;
        return v___x_1918_;
    } else {
        let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
        v___x_1919_ =
            l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__5;
        v___x_1920_ = l_Std_Format_joinSep___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__0(v_a_1917_, v___x_1919_);
        v___x_1921_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8_once), _init_l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__8);
        v___x_1922_ =
            l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__9;
        v___x_1923_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_1923_, 0, v___x_1922_);
        lean_ctor_set(v___x_1923_, 1, v___x_1920_);
        v___x_1924_ =
            l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg___closed__10;
        v___x_1925_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_1925_, 0, v___x_1923_);
        lean_ctor_set(v___x_1925_, 1, v___x_1924_);
        v___x_1926_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_1926_, 0, v___x_1921_);
        lean_ctor_set(v___x_1926_, 1, v___x_1925_);
        v___x_1927_ = l_Std_Format_fill(v___x_1926_);
        return v___x_1927_;
    }
}
pub unsafe fn _init_l_Lake_instReprCliError_repr___closed__8() -> *mut LeanObject {
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    v___x_1940_ = lean_unsigned_to_nat(2);
    v___x_1941_ = lean_nat_to_int(v___x_1940_);
    return v___x_1941_;
}
pub unsafe fn _init_l_Lake_instReprCliError_repr___closed__9() -> *mut LeanObject {
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    v___x_1942_ = lean_unsigned_to_nat(1);
    v___x_1943_ = lean_nat_to_int(v___x_1942_);
    return v___x_1943_;
}
pub unsafe fn l_Lake_instReprCliError_repr(
    mut v_x_2109_: *mut LeanObject,
    mut v_prec_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: u8 = 0;
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: u8 = 0;
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmd_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2146_: u8 = 0;
    let mut v___y_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2163_: u8 = 0;
    let mut v_arg_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2167_: u8 = 0;
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: u8 = 0;
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v_opt_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___y_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2211_: u8 = 0;
    let mut v_opt_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___y_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: u8 = 0;
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: u8 = 0;
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_opt_2239_: u32 = 0;
    let mut v___y_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opt_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2257_: u8 = 0;
    let mut v___y_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: u8 = 0;
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2274_: u8 = 0;
    let mut v_args_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_spec_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v___y_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2313_: u8 = 0;
    let mut v_spec_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___y_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut v_mod_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: u8 = 0;
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_path_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2353_: u8 = 0;
    let mut v___y_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: u8 = 0;
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: u8 = 0;
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_spec_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___y_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_type_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facet_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2400_: u8 = 0;
    let mut v___y_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: u8 = 0;
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2422_: u8 = 0;
    let mut v_target_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: u8 = 0;
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v___y_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2463_: u8 = 0;
    let mut v_pkg_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_spec_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___y_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: u8 = 0;
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: u8 = 0;
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut v_key_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v___y_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: u8 = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: u8 = 0;
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2511_: u8 = 0;
    let mut v_spec_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tooMany_2513_: u32 = 0;
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_facet_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2537_: u8 = 0;
    let mut v___y_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: u8 = 0;
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_spec_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___y_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u8 = 0;
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_script_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v___y_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2600_: u8 = 0;
    let mut v_script_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2604_: u8 = 0;
    let mut v___y_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: u8 = 0;
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v_spec_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v___y_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: u8 = 0;
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2642_: u8 = 0;
    let mut v_path_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___y_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: u8 = 0;
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: u8 = 0;
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expected_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_actual_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2680_: u8 = 0;
    let mut v___y_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u8 = 0;
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2702_: u8 = 0;
    let mut v_msg_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v___y_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: u8 = 0;
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut v_path_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___y_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u8 = 0;
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: u8 = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2109_) {
                0 => {
                    v___x_2139_ = lean_unsigned_to_nat(1024);
                    v___x_2140_ = lean_nat_dec_le(v___x_2139_, v_prec_2110_);
                    if v___x_2140_ == 0 {
                        v___x_2141_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2126_ = v___x_2141_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2142_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2126_ = v___x_2142_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v_cmd_2143_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2163_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2163_ == 0 {
                        v___x_2145_ = v_x_2109_;
                        v_isShared_2146_ = v_isSharedCheck_2163_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_cmd_2143_);
                        lean_dec(v_x_2109_);
                        v___x_2145_ = lean_box(0);
                        v_isShared_2146_ = v_isSharedCheck_2163_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_arg_2164_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2184_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2184_ == 0 {
                        v___x_2166_ = v_x_2109_;
                        v_isShared_2167_ = v_isSharedCheck_2184_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_arg_2164_);
                        lean_dec(v_x_2109_);
                        v___x_2166_ = lean_box(0);
                        v_isShared_2167_ = v_isSharedCheck_2184_;
                        state = 8;
                        continue;
                    }
                }
                3 => {
                    v_opt_2185_ = lean_ctor_get(v_x_2109_, 0);
                    v_arg_2186_ = lean_ctor_get(v_x_2109_, 1);
                    v_isSharedCheck_2211_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2211_ == 0 {
                        v___x_2188_ = v_x_2109_;
                        v_isShared_2189_ = v_isSharedCheck_2211_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_arg_2186_);
                        lean_inc(v_opt_2185_);
                        lean_dec(v_x_2109_);
                        v___x_2188_ = lean_box(0);
                        v_isShared_2189_ = v_isSharedCheck_2211_;
                        state = 11;
                        continue;
                    }
                }
                4 => {
                    v_opt_2212_ = lean_ctor_get(v_x_2109_, 0);
                    v_arg_2213_ = lean_ctor_get(v_x_2109_, 1);
                    v_isSharedCheck_2238_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v___x_2215_ = v_x_2109_;
                        v_isShared_2216_ = v_isSharedCheck_2238_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_arg_2213_);
                        lean_inc(v_opt_2212_);
                        lean_dec(v_x_2109_);
                        v___x_2215_ = lean_box(0);
                        v_isShared_2216_ = v_isSharedCheck_2238_;
                        state = 14;
                        continue;
                    }
                }
                5 => {
                    v_opt_2239_ = lean_ctor_get_uint32(v_x_2109_, 0 as u32);
                    lean_dec_ref_known(v_x_2109_, 0);
                    v___x_2250_ = lean_unsigned_to_nat(1024);
                    v___x_2251_ = lean_nat_dec_le(v___x_2250_, v_prec_2110_);
                    if v___x_2251_ == 0 {
                        v___x_2252_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2241_ = v___x_2252_;
                        state = 17;
                        continue;
                    } else {
                        v___x_2253_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2241_ = v___x_2253_;
                        state = 17;
                        continue;
                    }
                }
                6 => {
                    v_opt_2254_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2274_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2274_ == 0 {
                        v___x_2256_ = v_x_2109_;
                        v_isShared_2257_ = v_isSharedCheck_2274_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_opt_2254_);
                        lean_dec(v_x_2109_);
                        v___x_2256_ = lean_box(0);
                        v_isShared_2257_ = v_isSharedCheck_2274_;
                        state = 18;
                        continue;
                    }
                }
                7 => {
                    v_args_2275_ = lean_ctor_get(v_x_2109_, 0);
                    lean_inc(v_args_2275_);
                    lean_dec_ref_known(v_x_2109_, 1);
                    v___x_2285_ = lean_unsigned_to_nat(1024);
                    v___x_2286_ = lean_nat_dec_le(v___x_2285_, v_prec_2110_);
                    if v___x_2286_ == 0 {
                        v___x_2287_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2277_ = v___x_2287_;
                        state = 21;
                        continue;
                    } else {
                        v___x_2288_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2277_ = v___x_2288_;
                        state = 21;
                        continue;
                    }
                }
                8 => {
                    v___x_2289_ = lean_unsigned_to_nat(1024);
                    v___x_2290_ = lean_nat_dec_le(v___x_2289_, v_prec_2110_);
                    if v___x_2290_ == 0 {
                        v___x_2291_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2133_ = v___x_2291_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2292_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2133_ = v___x_2292_;
                        state = 4;
                        continue;
                    }
                }
                9 => {
                    v_spec_2293_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2313_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2313_ == 0 {
                        v___x_2295_ = v_x_2109_;
                        v_isShared_2296_ = v_isSharedCheck_2313_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_spec_2293_);
                        lean_dec(v_x_2109_);
                        v___x_2295_ = lean_box(0);
                        v_isShared_2296_ = v_isSharedCheck_2313_;
                        state = 22;
                        continue;
                    }
                }
                10 => {
                    v_spec_2314_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2334_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2334_ == 0 {
                        v___x_2316_ = v_x_2109_;
                        v_isShared_2317_ = v_isSharedCheck_2334_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_spec_2314_);
                        lean_dec(v_x_2109_);
                        v___x_2316_ = lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2334_;
                        state = 25;
                        continue;
                    }
                }
                11 => {
                    v_mod_2335_ = lean_ctor_get(v_x_2109_, 0);
                    lean_inc(v_mod_2335_);
                    lean_dec_ref_known(v_x_2109_, 1);
                    v___x_2346_ = lean_unsigned_to_nat(1024);
                    v___x_2347_ = lean_nat_dec_le(v___x_2346_, v_prec_2110_);
                    if v___x_2347_ == 0 {
                        v___x_2348_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2337_ = v___x_2348_;
                        state = 28;
                        continue;
                    } else {
                        v___x_2349_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2337_ = v___x_2349_;
                        state = 28;
                        continue;
                    }
                }
                12 => {
                    v_path_2350_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2374_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2374_ == 0 {
                        v___x_2352_ = v_x_2109_;
                        v_isShared_2353_ = v_isSharedCheck_2374_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_path_2350_);
                        lean_dec(v_x_2109_);
                        v___x_2352_ = lean_box(0);
                        v_isShared_2353_ = v_isSharedCheck_2374_;
                        state = 29;
                        continue;
                    }
                }
                13 => {
                    v_spec_2375_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2395_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2395_ == 0 {
                        v___x_2377_ = v_x_2109_;
                        v_isShared_2378_ = v_isSharedCheck_2395_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_spec_2375_);
                        lean_dec(v_x_2109_);
                        v___x_2377_ = lean_box(0);
                        v_isShared_2378_ = v_isSharedCheck_2395_;
                        state = 32;
                        continue;
                    }
                }
                14 => {
                    v_type_2396_ = lean_ctor_get(v_x_2109_, 0);
                    v_facet_2397_ = lean_ctor_get(v_x_2109_, 1);
                    v_isSharedCheck_2422_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2422_ == 0 {
                        v___x_2399_ = v_x_2109_;
                        v_isShared_2400_ = v_isSharedCheck_2422_;
                        state = 35;
                        continue;
                    } else {
                        lean_inc(v_facet_2397_);
                        lean_inc(v_type_2396_);
                        lean_dec(v_x_2109_);
                        v___x_2399_ = lean_box(0);
                        v_isShared_2400_ = v_isSharedCheck_2422_;
                        state = 35;
                        continue;
                    }
                }
                15 => {
                    v_target_2423_ = lean_ctor_get(v_x_2109_, 0);
                    lean_inc(v_target_2423_);
                    lean_dec_ref_known(v_x_2109_, 1);
                    v___x_2434_ = lean_unsigned_to_nat(1024);
                    v___x_2435_ = lean_nat_dec_le(v___x_2434_, v_prec_2110_);
                    if v___x_2435_ == 0 {
                        v___x_2436_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2425_ = v___x_2436_;
                        state = 38;
                        continue;
                    } else {
                        v___x_2437_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2425_ = v___x_2437_;
                        state = 38;
                        continue;
                    }
                }
                16 => {
                    v_pkg_2438_ = lean_ctor_get(v_x_2109_, 0);
                    v_mod_2439_ = lean_ctor_get(v_x_2109_, 1);
                    v_isSharedCheck_2463_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2463_ == 0 {
                        v___x_2441_ = v_x_2109_;
                        v_isShared_2442_ = v_isSharedCheck_2463_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_mod_2439_);
                        lean_inc(v_pkg_2438_);
                        lean_dec(v_x_2109_);
                        v___x_2441_ = lean_box(0);
                        v_isShared_2442_ = v_isSharedCheck_2463_;
                        state = 39;
                        continue;
                    }
                }
                17 => {
                    v_pkg_2464_ = lean_ctor_get(v_x_2109_, 0);
                    v_spec_2465_ = lean_ctor_get(v_x_2109_, 1);
                    v_isSharedCheck_2490_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2490_ == 0 {
                        v___x_2467_ = v_x_2109_;
                        v_isShared_2468_ = v_isSharedCheck_2490_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_spec_2465_);
                        lean_inc(v_pkg_2464_);
                        lean_dec(v_x_2109_);
                        v___x_2467_ = lean_box(0);
                        v_isShared_2468_ = v_isSharedCheck_2490_;
                        state = 42;
                        continue;
                    }
                }
                18 => {
                    v_key_2491_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2511_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2511_ == 0 {
                        v___x_2493_ = v_x_2109_;
                        v_isShared_2494_ = v_isSharedCheck_2511_;
                        state = 45;
                        continue;
                    } else {
                        lean_inc(v_key_2491_);
                        lean_dec(v_x_2109_);
                        v___x_2493_ = lean_box(0);
                        v_isShared_2494_ = v_isSharedCheck_2511_;
                        state = 45;
                        continue;
                    }
                }
                19 => {
                    v_spec_2512_ = lean_ctor_get(v_x_2109_, 0);
                    lean_inc_ref(v_spec_2512_);
                    v_tooMany_2513_ = lean_ctor_get_uint32(
                        v_x_2109_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    lean_dec_ref_known(v_x_2109_, 1);
                    v___x_2529_ = lean_unsigned_to_nat(1024);
                    v___x_2530_ = lean_nat_dec_le(v___x_2529_, v_prec_2110_);
                    if v___x_2530_ == 0 {
                        v___x_2531_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2515_ = v___x_2531_;
                        state = 48;
                        continue;
                    } else {
                        v___x_2532_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2515_ = v___x_2532_;
                        state = 48;
                        continue;
                    }
                }
                20 => {
                    v_target_2533_ = lean_ctor_get(v_x_2109_, 0);
                    v_facet_2534_ = lean_ctor_get(v_x_2109_, 1);
                    v_isSharedCheck_2558_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2558_ == 0 {
                        v___x_2536_ = v_x_2109_;
                        v_isShared_2537_ = v_isSharedCheck_2558_;
                        state = 49;
                        continue;
                    } else {
                        lean_inc(v_facet_2534_);
                        lean_inc(v_target_2533_);
                        lean_dec(v_x_2109_);
                        v___x_2536_ = lean_box(0);
                        v_isShared_2537_ = v_isSharedCheck_2558_;
                        state = 49;
                        continue;
                    }
                }
                21 => {
                    v_spec_2559_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2579_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2579_ == 0 {
                        v___x_2561_ = v_x_2109_;
                        v_isShared_2562_ = v_isSharedCheck_2579_;
                        state = 52;
                        continue;
                    } else {
                        lean_inc(v_spec_2559_);
                        lean_dec(v_x_2109_);
                        v___x_2561_ = lean_box(0);
                        v_isShared_2562_ = v_isSharedCheck_2579_;
                        state = 52;
                        continue;
                    }
                }
                22 => {
                    v_script_2580_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2600_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2600_ == 0 {
                        v___x_2582_ = v_x_2109_;
                        v_isShared_2583_ = v_isSharedCheck_2600_;
                        state = 55;
                        continue;
                    } else {
                        lean_inc(v_script_2580_);
                        lean_dec(v_x_2109_);
                        v___x_2582_ = lean_box(0);
                        v_isShared_2583_ = v_isSharedCheck_2600_;
                        state = 55;
                        continue;
                    }
                }
                23 => {
                    v_script_2601_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2621_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2621_ == 0 {
                        v___x_2603_ = v_x_2109_;
                        v_isShared_2604_ = v_isSharedCheck_2621_;
                        state = 58;
                        continue;
                    } else {
                        lean_inc(v_script_2601_);
                        lean_dec(v_x_2109_);
                        v___x_2603_ = lean_box(0);
                        v_isShared_2604_ = v_isSharedCheck_2621_;
                        state = 58;
                        continue;
                    }
                }
                24 => {
                    v_spec_2622_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2642_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2642_ == 0 {
                        v___x_2624_ = v_x_2109_;
                        v_isShared_2625_ = v_isSharedCheck_2642_;
                        state = 61;
                        continue;
                    } else {
                        lean_inc(v_spec_2622_);
                        lean_dec(v_x_2109_);
                        v___x_2624_ = lean_box(0);
                        v_isShared_2625_ = v_isSharedCheck_2642_;
                        state = 61;
                        continue;
                    }
                }
                25 => {
                    v_path_2643_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2667_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2667_ == 0 {
                        v___x_2645_ = v_x_2109_;
                        v_isShared_2646_ = v_isSharedCheck_2667_;
                        state = 64;
                        continue;
                    } else {
                        lean_inc(v_path_2643_);
                        lean_dec(v_x_2109_);
                        v___x_2645_ = lean_box(0);
                        v_isShared_2646_ = v_isSharedCheck_2667_;
                        state = 64;
                        continue;
                    }
                }
                26 => {
                    v___x_2668_ = lean_unsigned_to_nat(1024);
                    v___x_2669_ = lean_nat_dec_le(v___x_2668_, v_prec_2110_);
                    if v___x_2669_ == 0 {
                        v___x_2670_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2119_ = v___x_2670_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2671_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2119_ = v___x_2671_;
                        state = 2;
                        continue;
                    }
                }
                27 => {
                    v___x_2672_ = lean_unsigned_to_nat(1024);
                    v___x_2673_ = lean_nat_dec_le(v___x_2672_, v_prec_2110_);
                    if v___x_2673_ == 0 {
                        v___x_2674_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                            _init_l_Lake_instReprCliError_repr___closed__8,
                        );
                        v___y_2112_ = v___x_2674_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2675_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                            core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                            _init_l_Lake_instReprCliError_repr___closed__9,
                        );
                        v___y_2112_ = v___x_2675_;
                        state = 1;
                        continue;
                    }
                }
                28 => {
                    v_expected_2676_ = lean_ctor_get(v_x_2109_, 0);
                    v_actual_2677_ = lean_ctor_get(v_x_2109_, 1);
                    v_isSharedCheck_2702_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2702_ == 0 {
                        v___x_2679_ = v_x_2109_;
                        v_isShared_2680_ = v_isSharedCheck_2702_;
                        state = 67;
                        continue;
                    } else {
                        lean_inc(v_actual_2677_);
                        lean_inc(v_expected_2676_);
                        lean_dec(v_x_2109_);
                        v___x_2679_ = lean_box(0);
                        v_isShared_2680_ = v_isSharedCheck_2702_;
                        state = 67;
                        continue;
                    }
                }
                29 => {
                    v_msg_2703_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2723_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2723_ == 0 {
                        v___x_2705_ = v_x_2109_;
                        v_isShared_2706_ = v_isSharedCheck_2723_;
                        state = 70;
                        continue;
                    } else {
                        lean_inc(v_msg_2703_);
                        lean_dec(v_x_2109_);
                        v___x_2705_ = lean_box(0);
                        v_isShared_2706_ = v_isSharedCheck_2723_;
                        state = 70;
                        continue;
                    }
                }
                _ => {
                    v_path_2724_ = lean_ctor_get(v_x_2109_, 0);
                    v_isSharedCheck_2748_ = (!lean_is_exclusive(v_x_2109_)) as u8;
                    if v_isSharedCheck_2748_ == 0 {
                        v___x_2726_ = v_x_2109_;
                        v_isShared_2727_ = v_isSharedCheck_2748_;
                        state = 73;
                        continue;
                    } else {
                        lean_inc(v_path_2724_);
                        lean_dec(v_x_2109_);
                        v___x_2726_ = lean_box(0);
                        v_isShared_2727_ = v_isSharedCheck_2748_;
                        state = 73;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2113_ = l_Lake_instReprCliError_repr___closed__1;
                lean_inc(v___y_2112_);
                v___x_2114_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v___y_2112_);
                lean_ctor_set(v___x_2114_, 1, v___x_2113_);
                v___x_2115_ = 0;
                v___x_2116_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2116_, 0, v___x_2114_);
                lean_ctor_set_uint8(
                    v___x_2116_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2115_,
                );
                v___x_2117_ = l_Repr_addAppParen(v___x_2116_, v_prec_2110_);
                return v___x_2117_;
            }
            2 => {
                v___x_2120_ = l_Lake_instReprCliError_repr___closed__3;
                lean_inc(v___y_2119_);
                v___x_2121_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2121_, 0, v___y_2119_);
                lean_ctor_set(v___x_2121_, 1, v___x_2120_);
                v___x_2122_ = 0;
                v___x_2123_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2123_, 0, v___x_2121_);
                lean_ctor_set_uint8(
                    v___x_2123_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2122_,
                );
                v___x_2124_ = l_Repr_addAppParen(v___x_2123_, v_prec_2110_);
                return v___x_2124_;
            }
            3 => {
                v___x_2127_ = l_Lake_instReprCliError_repr___closed__5;
                lean_inc(v___y_2126_);
                v___x_2128_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2128_, 0, v___y_2126_);
                lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                v___x_2129_ = 0;
                v___x_2130_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2130_, 0, v___x_2128_);
                lean_ctor_set_uint8(
                    v___x_2130_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2129_,
                );
                v___x_2131_ = l_Repr_addAppParen(v___x_2130_, v_prec_2110_);
                return v___x_2131_;
            }
            4 => {
                v___x_2134_ = l_Lake_instReprCliError_repr___closed__7;
                lean_inc(v___y_2133_);
                v___x_2135_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2135_, 0, v___y_2133_);
                lean_ctor_set(v___x_2135_, 1, v___x_2134_);
                v___x_2136_ = 0;
                v___x_2137_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2137_, 0, v___x_2135_);
                lean_ctor_set_uint8(
                    v___x_2137_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2136_,
                );
                v___x_2138_ = l_Repr_addAppParen(v___x_2137_, v_prec_2110_);
                return v___x_2138_;
            }
            5 => {
                v___x_2159_ = lean_unsigned_to_nat(1024);
                v___x_2160_ = lean_nat_dec_le(v___x_2159_, v_prec_2110_);
                if v___x_2160_ == 0 {
                    v___x_2161_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2148_ = v___x_2161_;
                    state = 6;
                    continue;
                } else {
                    v___x_2162_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2148_ = v___x_2162_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2149_ = l_Lake_instReprCliError_repr___closed__12;
                v___x_2150_ = l_String_quote(v_cmd_2143_);
                if v_isShared_2146_ == 0 {
                    lean_ctor_set_tag(v___x_2145_, 3);
                    lean_ctor_set(v___x_2145_, 0, v___x_2150_);
                    v___x_2152_ = v___x_2145_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2158_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2150_);
                    v___x_2152_ = v_reuseFailAlloc_2158_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2153_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2153_, 0, v___x_2149_);
                lean_ctor_set(v___x_2153_, 1, v___x_2152_);
                lean_inc(v___y_2148_);
                v___x_2154_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2154_, 0, v___y_2148_);
                lean_ctor_set(v___x_2154_, 1, v___x_2153_);
                v___x_2155_ = 0;
                v___x_2156_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2156_, 0, v___x_2154_);
                lean_ctor_set_uint8(
                    v___x_2156_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2155_,
                );
                v___x_2157_ = l_Repr_addAppParen(v___x_2156_, v_prec_2110_);
                return v___x_2157_;
            }
            8 => {
                v___x_2180_ = lean_unsigned_to_nat(1024);
                v___x_2181_ = lean_nat_dec_le(v___x_2180_, v_prec_2110_);
                if v___x_2181_ == 0 {
                    v___x_2182_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2169_ = v___x_2182_;
                    state = 9;
                    continue;
                } else {
                    v___x_2183_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2169_ = v___x_2183_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2170_ = l_Lake_instReprCliError_repr___closed__15;
                v___x_2171_ = l_String_quote(v_arg_2164_);
                if v_isShared_2167_ == 0 {
                    lean_ctor_set_tag(v___x_2166_, 3);
                    lean_ctor_set(v___x_2166_, 0, v___x_2171_);
                    v___x_2173_ = v___x_2166_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2179_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2171_);
                    v___x_2173_ = v_reuseFailAlloc_2179_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2174_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2174_, 0, v___x_2170_);
                lean_ctor_set(v___x_2174_, 1, v___x_2173_);
                lean_inc(v___y_2169_);
                v___x_2175_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2175_, 0, v___y_2169_);
                lean_ctor_set(v___x_2175_, 1, v___x_2174_);
                v___x_2176_ = 0;
                v___x_2177_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2177_, 0, v___x_2175_);
                lean_ctor_set_uint8(
                    v___x_2177_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2176_,
                );
                v___x_2178_ = l_Repr_addAppParen(v___x_2177_, v_prec_2110_);
                return v___x_2178_;
            }
            11 => {
                v___x_2207_ = lean_unsigned_to_nat(1024);
                v___x_2208_ = lean_nat_dec_le(v___x_2207_, v_prec_2110_);
                if v___x_2208_ == 0 {
                    v___x_2209_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2191_ = v___x_2209_;
                    state = 12;
                    continue;
                } else {
                    v___x_2210_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2191_ = v___x_2210_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_2192_ = lean_box(1);
                v___x_2193_ = l_Lake_instReprCliError_repr___closed__18;
                v___x_2194_ = l_String_quote(v_opt_2185_);
                v___x_2195_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2195_, 0, v___x_2194_);
                if v_isShared_2189_ == 0 {
                    lean_ctor_set_tag(v___x_2188_, 5);
                    lean_ctor_set(v___x_2188_, 1, v___x_2195_);
                    lean_ctor_set(v___x_2188_, 0, v___x_2193_);
                    v___x_2197_ = v___x_2188_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2206_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2193_);
                    lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2195_);
                    v___x_2197_ = v_reuseFailAlloc_2206_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2198_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2198_, 0, v___x_2197_);
                lean_ctor_set(v___x_2198_, 1, v___x_2192_);
                v___x_2199_ = l_String_quote(v_arg_2186_);
                v___x_2200_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2200_, 0, v___x_2199_);
                v___x_2201_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2201_, 0, v___x_2198_);
                lean_ctor_set(v___x_2201_, 1, v___x_2200_);
                lean_inc(v___y_2191_);
                v___x_2202_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2202_, 0, v___y_2191_);
                lean_ctor_set(v___x_2202_, 1, v___x_2201_);
                v___x_2203_ = 0;
                v___x_2204_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2204_, 0, v___x_2202_);
                lean_ctor_set_uint8(
                    v___x_2204_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2203_,
                );
                v___x_2205_ = l_Repr_addAppParen(v___x_2204_, v_prec_2110_);
                return v___x_2205_;
            }
            14 => {
                v___x_2234_ = lean_unsigned_to_nat(1024);
                v___x_2235_ = lean_nat_dec_le(v___x_2234_, v_prec_2110_);
                if v___x_2235_ == 0 {
                    v___x_2236_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2218_ = v___x_2236_;
                    state = 15;
                    continue;
                } else {
                    v___x_2237_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2218_ = v___x_2237_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2219_ = lean_box(1);
                v___x_2220_ = l_Lake_instReprCliError_repr___closed__21;
                v___x_2221_ = l_String_quote(v_opt_2212_);
                v___x_2222_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2222_, 0, v___x_2221_);
                if v_isShared_2216_ == 0 {
                    lean_ctor_set_tag(v___x_2215_, 5);
                    lean_ctor_set(v___x_2215_, 1, v___x_2222_);
                    lean_ctor_set(v___x_2215_, 0, v___x_2220_);
                    v___x_2224_ = v___x_2215_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2233_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2220_);
                    lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2222_);
                    v___x_2224_ = v_reuseFailAlloc_2233_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_2225_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2225_, 0, v___x_2224_);
                lean_ctor_set(v___x_2225_, 1, v___x_2219_);
                v___x_2226_ = l_String_quote(v_arg_2213_);
                v___x_2227_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2227_, 0, v___x_2226_);
                v___x_2228_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2228_, 0, v___x_2225_);
                lean_ctor_set(v___x_2228_, 1, v___x_2227_);
                lean_inc(v___y_2218_);
                v___x_2229_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2229_, 0, v___y_2218_);
                lean_ctor_set(v___x_2229_, 1, v___x_2228_);
                v___x_2230_ = 0;
                v___x_2231_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2231_, 0, v___x_2229_);
                lean_ctor_set_uint8(
                    v___x_2231_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2230_,
                );
                v___x_2232_ = l_Repr_addAppParen(v___x_2231_, v_prec_2110_);
                return v___x_2232_;
            }
            17 => {
                v___x_2242_ = l_Lake_instReprCliError_repr___closed__24;
                v___x_2243_ = l_Char_quote(v_opt_2239_);
                v___x_2244_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2244_, 0, v___x_2243_);
                v___x_2245_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2245_, 0, v___x_2242_);
                lean_ctor_set(v___x_2245_, 1, v___x_2244_);
                lean_inc(v___y_2241_);
                v___x_2246_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2246_, 0, v___y_2241_);
                lean_ctor_set(v___x_2246_, 1, v___x_2245_);
                v___x_2247_ = 0;
                v___x_2248_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2248_, 0, v___x_2246_);
                lean_ctor_set_uint8(
                    v___x_2248_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2247_,
                );
                v___x_2249_ = l_Repr_addAppParen(v___x_2248_, v_prec_2110_);
                return v___x_2249_;
            }
            18 => {
                v___x_2270_ = lean_unsigned_to_nat(1024);
                v___x_2271_ = lean_nat_dec_le(v___x_2270_, v_prec_2110_);
                if v___x_2271_ == 0 {
                    v___x_2272_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2259_ = v___x_2272_;
                    state = 19;
                    continue;
                } else {
                    v___x_2273_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2259_ = v___x_2273_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_2260_ = l_Lake_instReprCliError_repr___closed__27;
                v___x_2261_ = l_String_quote(v_opt_2254_);
                if v_isShared_2257_ == 0 {
                    lean_ctor_set_tag(v___x_2256_, 3);
                    lean_ctor_set(v___x_2256_, 0, v___x_2261_);
                    v___x_2263_ = v___x_2256_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2261_);
                    v___x_2263_ = v_reuseFailAlloc_2269_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_2264_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2264_, 0, v___x_2260_);
                lean_ctor_set(v___x_2264_, 1, v___x_2263_);
                lean_inc(v___y_2259_);
                v___x_2265_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2265_, 0, v___y_2259_);
                lean_ctor_set(v___x_2265_, 1, v___x_2264_);
                v___x_2266_ = 0;
                v___x_2267_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2267_, 0, v___x_2265_);
                lean_ctor_set_uint8(
                    v___x_2267_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2266_,
                );
                v___x_2268_ = l_Repr_addAppParen(v___x_2267_, v_prec_2110_);
                return v___x_2268_;
            }
            21 => {
                v___x_2278_ = l_Lake_instReprCliError_repr___closed__30;
                v___x_2279_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(
                    v_args_2275_,
                );
                v___x_2280_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2280_, 0, v___x_2278_);
                lean_ctor_set(v___x_2280_, 1, v___x_2279_);
                lean_inc(v___y_2277_);
                v___x_2281_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2281_, 0, v___y_2277_);
                lean_ctor_set(v___x_2281_, 1, v___x_2280_);
                v___x_2282_ = 0;
                v___x_2283_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2283_, 0, v___x_2281_);
                lean_ctor_set_uint8(
                    v___x_2283_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2282_,
                );
                v___x_2284_ = l_Repr_addAppParen(v___x_2283_, v_prec_2110_);
                return v___x_2284_;
            }
            22 => {
                v___x_2309_ = lean_unsigned_to_nat(1024);
                v___x_2310_ = lean_nat_dec_le(v___x_2309_, v_prec_2110_);
                if v___x_2310_ == 0 {
                    v___x_2311_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2298_ = v___x_2311_;
                    state = 23;
                    continue;
                } else {
                    v___x_2312_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2298_ = v___x_2312_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_2299_ = l_Lake_instReprCliError_repr___closed__33;
                v___x_2300_ = l_String_quote(v_spec_2293_);
                if v_isShared_2296_ == 0 {
                    lean_ctor_set_tag(v___x_2295_, 3);
                    lean_ctor_set(v___x_2295_, 0, v___x_2300_);
                    v___x_2302_ = v___x_2295_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2300_);
                    v___x_2302_ = v_reuseFailAlloc_2308_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_2303_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2303_, 0, v___x_2299_);
                lean_ctor_set(v___x_2303_, 1, v___x_2302_);
                lean_inc(v___y_2298_);
                v___x_2304_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2304_, 0, v___y_2298_);
                lean_ctor_set(v___x_2304_, 1, v___x_2303_);
                v___x_2305_ = 0;
                v___x_2306_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2306_, 0, v___x_2304_);
                lean_ctor_set_uint8(
                    v___x_2306_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2305_,
                );
                v___x_2307_ = l_Repr_addAppParen(v___x_2306_, v_prec_2110_);
                return v___x_2307_;
            }
            25 => {
                v___x_2330_ = lean_unsigned_to_nat(1024);
                v___x_2331_ = lean_nat_dec_le(v___x_2330_, v_prec_2110_);
                if v___x_2331_ == 0 {
                    v___x_2332_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2319_ = v___x_2332_;
                    state = 26;
                    continue;
                } else {
                    v___x_2333_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2319_ = v___x_2333_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_2320_ = l_Lake_instReprCliError_repr___closed__36;
                v___x_2321_ = l_String_quote(v_spec_2314_);
                if v_isShared_2317_ == 0 {
                    lean_ctor_set_tag(v___x_2316_, 3);
                    lean_ctor_set(v___x_2316_, 0, v___x_2321_);
                    v___x_2323_ = v___x_2316_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2329_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2321_);
                    v___x_2323_ = v_reuseFailAlloc_2329_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_2324_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2324_, 0, v___x_2320_);
                lean_ctor_set(v___x_2324_, 1, v___x_2323_);
                lean_inc(v___y_2319_);
                v___x_2325_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2325_, 0, v___y_2319_);
                lean_ctor_set(v___x_2325_, 1, v___x_2324_);
                v___x_2326_ = 0;
                v___x_2327_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2327_, 0, v___x_2325_);
                lean_ctor_set_uint8(
                    v___x_2327_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2326_,
                );
                v___x_2328_ = l_Repr_addAppParen(v___x_2327_, v_prec_2110_);
                return v___x_2328_;
            }
            28 => {
                v___x_2338_ = l_Lake_instReprCliError_repr___closed__39;
                v___x_2339_ = lean_unsigned_to_nat(1024);
                v___x_2340_ = l_Lean_Name_reprPrec(v_mod_2335_, v___x_2339_);
                v___x_2341_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2341_, 0, v___x_2338_);
                lean_ctor_set(v___x_2341_, 1, v___x_2340_);
                lean_inc(v___y_2337_);
                v___x_2342_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2342_, 0, v___y_2337_);
                lean_ctor_set(v___x_2342_, 1, v___x_2341_);
                v___x_2343_ = 0;
                v___x_2344_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2344_, 0, v___x_2342_);
                lean_ctor_set_uint8(
                    v___x_2344_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2343_,
                );
                v___x_2345_ = l_Repr_addAppParen(v___x_2344_, v_prec_2110_);
                return v___x_2345_;
            }
            29 => {
                v___x_2370_ = lean_unsigned_to_nat(1024);
                v___x_2371_ = lean_nat_dec_le(v___x_2370_, v_prec_2110_);
                if v___x_2371_ == 0 {
                    v___x_2372_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2355_ = v___x_2372_;
                    state = 30;
                    continue;
                } else {
                    v___x_2373_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2355_ = v___x_2373_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2356_ = l_Lake_instReprCliError_repr___closed__42;
                v___x_2357_ = lean_unsigned_to_nat(1024);
                v___x_2358_ = l_Lake_instReprCliError_repr___closed__44;
                v___x_2359_ = l_String_quote(v_path_2350_);
                if v_isShared_2353_ == 0 {
                    lean_ctor_set_tag(v___x_2352_, 3);
                    lean_ctor_set(v___x_2352_, 0, v___x_2359_);
                    v___x_2361_ = v___x_2352_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2359_);
                    v___x_2361_ = v_reuseFailAlloc_2369_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                v___x_2362_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2362_, 0, v___x_2358_);
                lean_ctor_set(v___x_2362_, 1, v___x_2361_);
                v___x_2363_ = l_Repr_addAppParen(v___x_2362_, v___x_2357_);
                v___x_2364_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2364_, 0, v___x_2356_);
                lean_ctor_set(v___x_2364_, 1, v___x_2363_);
                lean_inc(v___y_2355_);
                v___x_2365_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2365_, 0, v___y_2355_);
                lean_ctor_set(v___x_2365_, 1, v___x_2364_);
                v___x_2366_ = 0;
                v___x_2367_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2367_, 0, v___x_2365_);
                lean_ctor_set_uint8(
                    v___x_2367_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2366_,
                );
                v___x_2368_ = l_Repr_addAppParen(v___x_2367_, v_prec_2110_);
                return v___x_2368_;
            }
            32 => {
                v___x_2391_ = lean_unsigned_to_nat(1024);
                v___x_2392_ = lean_nat_dec_le(v___x_2391_, v_prec_2110_);
                if v___x_2392_ == 0 {
                    v___x_2393_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2380_ = v___x_2393_;
                    state = 33;
                    continue;
                } else {
                    v___x_2394_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2380_ = v___x_2394_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_2381_ = l_Lake_instReprCliError_repr___closed__47;
                v___x_2382_ = l_String_quote(v_spec_2375_);
                if v_isShared_2378_ == 0 {
                    lean_ctor_set_tag(v___x_2377_, 3);
                    lean_ctor_set(v___x_2377_, 0, v___x_2382_);
                    v___x_2384_ = v___x_2377_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2390_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2382_);
                    v___x_2384_ = v_reuseFailAlloc_2390_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___x_2385_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2385_, 0, v___x_2381_);
                lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                lean_inc(v___y_2380_);
                v___x_2386_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2386_, 0, v___y_2380_);
                lean_ctor_set(v___x_2386_, 1, v___x_2385_);
                v___x_2387_ = 0;
                v___x_2388_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2388_, 0, v___x_2386_);
                lean_ctor_set_uint8(
                    v___x_2388_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2387_,
                );
                v___x_2389_ = l_Repr_addAppParen(v___x_2388_, v_prec_2110_);
                return v___x_2389_;
            }
            35 => {
                v___x_2418_ = lean_unsigned_to_nat(1024);
                v___x_2419_ = lean_nat_dec_le(v___x_2418_, v_prec_2110_);
                if v___x_2419_ == 0 {
                    v___x_2420_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2402_ = v___x_2420_;
                    state = 36;
                    continue;
                } else {
                    v___x_2421_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2402_ = v___x_2421_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___x_2403_ = lean_box(1);
                v___x_2404_ = l_Lake_instReprCliError_repr___closed__50;
                v___x_2405_ = l_String_quote(v_type_2396_);
                v___x_2406_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2406_, 0, v___x_2405_);
                if v_isShared_2400_ == 0 {
                    lean_ctor_set_tag(v___x_2399_, 5);
                    lean_ctor_set(v___x_2399_, 1, v___x_2406_);
                    lean_ctor_set(v___x_2399_, 0, v___x_2404_);
                    v___x_2408_ = v___x_2399_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2404_);
                    lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2406_);
                    v___x_2408_ = v_reuseFailAlloc_2417_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_2409_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2409_, 0, v___x_2408_);
                lean_ctor_set(v___x_2409_, 1, v___x_2403_);
                v___x_2410_ = lean_unsigned_to_nat(1024);
                v___x_2411_ = l_Lean_Name_reprPrec(v_facet_2397_, v___x_2410_);
                v___x_2412_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2412_, 0, v___x_2409_);
                lean_ctor_set(v___x_2412_, 1, v___x_2411_);
                lean_inc(v___y_2402_);
                v___x_2413_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2413_, 0, v___y_2402_);
                lean_ctor_set(v___x_2413_, 1, v___x_2412_);
                v___x_2414_ = 0;
                v___x_2415_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2415_, 0, v___x_2413_);
                lean_ctor_set_uint8(
                    v___x_2415_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2414_,
                );
                v___x_2416_ = l_Repr_addAppParen(v___x_2415_, v_prec_2110_);
                return v___x_2416_;
            }
            38 => {
                v___x_2426_ = l_Lake_instReprCliError_repr___closed__53;
                v___x_2427_ = lean_unsigned_to_nat(1024);
                v___x_2428_ = l_Lean_Name_reprPrec(v_target_2423_, v___x_2427_);
                v___x_2429_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2429_, 0, v___x_2426_);
                lean_ctor_set(v___x_2429_, 1, v___x_2428_);
                lean_inc(v___y_2425_);
                v___x_2430_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2430_, 0, v___y_2425_);
                lean_ctor_set(v___x_2430_, 1, v___x_2429_);
                v___x_2431_ = 0;
                v___x_2432_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2432_, 0, v___x_2430_);
                lean_ctor_set_uint8(
                    v___x_2432_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2431_,
                );
                v___x_2433_ = l_Repr_addAppParen(v___x_2432_, v_prec_2110_);
                return v___x_2433_;
            }
            39 => {
                v___x_2459_ = lean_unsigned_to_nat(1024);
                v___x_2460_ = lean_nat_dec_le(v___x_2459_, v_prec_2110_);
                if v___x_2460_ == 0 {
                    v___x_2461_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2444_ = v___x_2461_;
                    state = 40;
                    continue;
                } else {
                    v___x_2462_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2444_ = v___x_2462_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                v___x_2445_ = lean_box(1);
                v___x_2446_ = l_Lake_instReprCliError_repr___closed__56;
                v___x_2447_ = lean_unsigned_to_nat(1024);
                v___x_2448_ = l_Lean_Name_reprPrec(v_pkg_2438_, v___x_2447_);
                if v_isShared_2442_ == 0 {
                    lean_ctor_set_tag(v___x_2441_, 5);
                    lean_ctor_set(v___x_2441_, 1, v___x_2448_);
                    lean_ctor_set(v___x_2441_, 0, v___x_2446_);
                    v___x_2450_ = v___x_2441_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2446_);
                    lean_ctor_set(v_reuseFailAlloc_2458_, 1, v___x_2448_);
                    v___x_2450_ = v_reuseFailAlloc_2458_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                v___x_2451_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2451_, 0, v___x_2450_);
                lean_ctor_set(v___x_2451_, 1, v___x_2445_);
                v___x_2452_ = l_Lean_Name_reprPrec(v_mod_2439_, v___x_2447_);
                v___x_2453_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2453_, 0, v___x_2451_);
                lean_ctor_set(v___x_2453_, 1, v___x_2452_);
                lean_inc(v___y_2444_);
                v___x_2454_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2454_, 0, v___y_2444_);
                lean_ctor_set(v___x_2454_, 1, v___x_2453_);
                v___x_2455_ = 0;
                v___x_2456_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2456_, 0, v___x_2454_);
                lean_ctor_set_uint8(
                    v___x_2456_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2455_,
                );
                v___x_2457_ = l_Repr_addAppParen(v___x_2456_, v_prec_2110_);
                return v___x_2457_;
            }
            42 => {
                v___x_2486_ = lean_unsigned_to_nat(1024);
                v___x_2487_ = lean_nat_dec_le(v___x_2486_, v_prec_2110_);
                if v___x_2487_ == 0 {
                    v___x_2488_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2470_ = v___x_2488_;
                    state = 43;
                    continue;
                } else {
                    v___x_2489_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2470_ = v___x_2489_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                v___x_2471_ = lean_box(1);
                v___x_2472_ = l_Lake_instReprCliError_repr___closed__59;
                v___x_2473_ = lean_unsigned_to_nat(1024);
                v___x_2474_ = l_Lean_Name_reprPrec(v_pkg_2464_, v___x_2473_);
                if v_isShared_2468_ == 0 {
                    lean_ctor_set_tag(v___x_2467_, 5);
                    lean_ctor_set(v___x_2467_, 1, v___x_2474_);
                    lean_ctor_set(v___x_2467_, 0, v___x_2472_);
                    v___x_2476_ = v___x_2467_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2472_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2474_);
                    v___x_2476_ = v_reuseFailAlloc_2485_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_2477_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2477_, 0, v___x_2476_);
                lean_ctor_set(v___x_2477_, 1, v___x_2471_);
                v___x_2478_ = l_String_quote(v_spec_2465_);
                v___x_2479_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2479_, 0, v___x_2478_);
                v___x_2480_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2480_, 0, v___x_2477_);
                lean_ctor_set(v___x_2480_, 1, v___x_2479_);
                lean_inc(v___y_2470_);
                v___x_2481_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2481_, 0, v___y_2470_);
                lean_ctor_set(v___x_2481_, 1, v___x_2480_);
                v___x_2482_ = 0;
                v___x_2483_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2483_, 0, v___x_2481_);
                lean_ctor_set_uint8(
                    v___x_2483_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2482_,
                );
                v___x_2484_ = l_Repr_addAppParen(v___x_2483_, v_prec_2110_);
                return v___x_2484_;
            }
            45 => {
                v___x_2507_ = lean_unsigned_to_nat(1024);
                v___x_2508_ = lean_nat_dec_le(v___x_2507_, v_prec_2110_);
                if v___x_2508_ == 0 {
                    v___x_2509_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2496_ = v___x_2509_;
                    state = 46;
                    continue;
                } else {
                    v___x_2510_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2496_ = v___x_2510_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                v___x_2497_ = l_Lake_instReprCliError_repr___closed__62;
                v___x_2498_ = l_String_quote(v_key_2491_);
                if v_isShared_2494_ == 0 {
                    lean_ctor_set_tag(v___x_2493_, 3);
                    lean_ctor_set(v___x_2493_, 0, v___x_2498_);
                    v___x_2500_ = v___x_2493_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2506_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2498_);
                    v___x_2500_ = v_reuseFailAlloc_2506_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                v___x_2501_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2501_, 0, v___x_2497_);
                lean_ctor_set(v___x_2501_, 1, v___x_2500_);
                lean_inc(v___y_2496_);
                v___x_2502_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2502_, 0, v___y_2496_);
                lean_ctor_set(v___x_2502_, 1, v___x_2501_);
                v___x_2503_ = 0;
                v___x_2504_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2504_, 0, v___x_2502_);
                lean_ctor_set_uint8(
                    v___x_2504_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2503_,
                );
                v___x_2505_ = l_Repr_addAppParen(v___x_2504_, v_prec_2110_);
                return v___x_2505_;
            }
            48 => {
                v___x_2516_ = lean_box(1);
                v___x_2517_ = l_Lake_instReprCliError_repr___closed__65;
                v___x_2518_ = l_String_quote(v_spec_2512_);
                v___x_2519_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2519_, 0, v___x_2518_);
                v___x_2520_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2520_, 0, v___x_2517_);
                lean_ctor_set(v___x_2520_, 1, v___x_2519_);
                v___x_2521_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2521_, 0, v___x_2520_);
                lean_ctor_set(v___x_2521_, 1, v___x_2516_);
                v___x_2522_ = l_Char_quote(v_tooMany_2513_);
                v___x_2523_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2523_, 0, v___x_2522_);
                v___x_2524_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2524_, 0, v___x_2521_);
                lean_ctor_set(v___x_2524_, 1, v___x_2523_);
                lean_inc(v___y_2515_);
                v___x_2525_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2525_, 0, v___y_2515_);
                lean_ctor_set(v___x_2525_, 1, v___x_2524_);
                v___x_2526_ = 0;
                v___x_2527_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2527_, 0, v___x_2525_);
                lean_ctor_set_uint8(
                    v___x_2527_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2526_,
                );
                v___x_2528_ = l_Repr_addAppParen(v___x_2527_, v_prec_2110_);
                return v___x_2528_;
            }
            49 => {
                v___x_2554_ = lean_unsigned_to_nat(1024);
                v___x_2555_ = lean_nat_dec_le(v___x_2554_, v_prec_2110_);
                if v___x_2555_ == 0 {
                    v___x_2556_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2539_ = v___x_2556_;
                    state = 50;
                    continue;
                } else {
                    v___x_2557_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2539_ = v___x_2557_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                v___x_2540_ = lean_box(1);
                v___x_2541_ = l_Lake_instReprCliError_repr___closed__68;
                v___x_2542_ = lean_unsigned_to_nat(1024);
                v___x_2543_ = l_Lean_Name_reprPrec(v_target_2533_, v___x_2542_);
                if v_isShared_2537_ == 0 {
                    lean_ctor_set_tag(v___x_2536_, 5);
                    lean_ctor_set(v___x_2536_, 1, v___x_2543_);
                    lean_ctor_set(v___x_2536_, 0, v___x_2541_);
                    v___x_2545_ = v___x_2536_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_2553_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2541_);
                    lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2543_);
                    v___x_2545_ = v_reuseFailAlloc_2553_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___x_2546_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2546_, 0, v___x_2545_);
                lean_ctor_set(v___x_2546_, 1, v___x_2540_);
                v___x_2547_ = l_Lean_Name_reprPrec(v_facet_2534_, v___x_2542_);
                v___x_2548_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2548_, 0, v___x_2546_);
                lean_ctor_set(v___x_2548_, 1, v___x_2547_);
                lean_inc(v___y_2539_);
                v___x_2549_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2549_, 0, v___y_2539_);
                lean_ctor_set(v___x_2549_, 1, v___x_2548_);
                v___x_2550_ = 0;
                v___x_2551_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2551_, 0, v___x_2549_);
                lean_ctor_set_uint8(
                    v___x_2551_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2550_,
                );
                v___x_2552_ = l_Repr_addAppParen(v___x_2551_, v_prec_2110_);
                return v___x_2552_;
            }
            52 => {
                v___x_2575_ = lean_unsigned_to_nat(1024);
                v___x_2576_ = lean_nat_dec_le(v___x_2575_, v_prec_2110_);
                if v___x_2576_ == 0 {
                    v___x_2577_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2564_ = v___x_2577_;
                    state = 53;
                    continue;
                } else {
                    v___x_2578_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2564_ = v___x_2578_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                v___x_2565_ = l_Lake_instReprCliError_repr___closed__71;
                v___x_2566_ = l_String_quote(v_spec_2559_);
                if v_isShared_2562_ == 0 {
                    lean_ctor_set_tag(v___x_2561_, 3);
                    lean_ctor_set(v___x_2561_, 0, v___x_2566_);
                    v___x_2568_ = v___x_2561_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2566_);
                    v___x_2568_ = v_reuseFailAlloc_2574_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v___x_2569_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2569_, 0, v___x_2565_);
                lean_ctor_set(v___x_2569_, 1, v___x_2568_);
                lean_inc(v___y_2564_);
                v___x_2570_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2570_, 0, v___y_2564_);
                lean_ctor_set(v___x_2570_, 1, v___x_2569_);
                v___x_2571_ = 0;
                v___x_2572_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2572_, 0, v___x_2570_);
                lean_ctor_set_uint8(
                    v___x_2572_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2571_,
                );
                v___x_2573_ = l_Repr_addAppParen(v___x_2572_, v_prec_2110_);
                return v___x_2573_;
            }
            55 => {
                v___x_2596_ = lean_unsigned_to_nat(1024);
                v___x_2597_ = lean_nat_dec_le(v___x_2596_, v_prec_2110_);
                if v___x_2597_ == 0 {
                    v___x_2598_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2585_ = v___x_2598_;
                    state = 56;
                    continue;
                } else {
                    v___x_2599_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2585_ = v___x_2599_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v___x_2586_ = l_Lake_instReprCliError_repr___closed__74;
                v___x_2587_ = l_String_quote(v_script_2580_);
                if v_isShared_2583_ == 0 {
                    lean_ctor_set_tag(v___x_2582_, 3);
                    lean_ctor_set(v___x_2582_, 0, v___x_2587_);
                    v___x_2589_ = v___x_2582_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_2595_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2587_);
                    v___x_2589_ = v_reuseFailAlloc_2595_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                v___x_2590_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2590_, 0, v___x_2586_);
                lean_ctor_set(v___x_2590_, 1, v___x_2589_);
                lean_inc(v___y_2585_);
                v___x_2591_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2591_, 0, v___y_2585_);
                lean_ctor_set(v___x_2591_, 1, v___x_2590_);
                v___x_2592_ = 0;
                v___x_2593_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2593_, 0, v___x_2591_);
                lean_ctor_set_uint8(
                    v___x_2593_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2592_,
                );
                v___x_2594_ = l_Repr_addAppParen(v___x_2593_, v_prec_2110_);
                return v___x_2594_;
            }
            58 => {
                v___x_2617_ = lean_unsigned_to_nat(1024);
                v___x_2618_ = lean_nat_dec_le(v___x_2617_, v_prec_2110_);
                if v___x_2618_ == 0 {
                    v___x_2619_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2606_ = v___x_2619_;
                    state = 59;
                    continue;
                } else {
                    v___x_2620_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2606_ = v___x_2620_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                v___x_2607_ = l_Lake_instReprCliError_repr___closed__77;
                v___x_2608_ = l_String_quote(v_script_2601_);
                if v_isShared_2604_ == 0 {
                    lean_ctor_set_tag(v___x_2603_, 3);
                    lean_ctor_set(v___x_2603_, 0, v___x_2608_);
                    v___x_2610_ = v___x_2603_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2616_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2608_);
                    v___x_2610_ = v_reuseFailAlloc_2616_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_2611_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2611_, 0, v___x_2607_);
                lean_ctor_set(v___x_2611_, 1, v___x_2610_);
                lean_inc(v___y_2606_);
                v___x_2612_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2612_, 0, v___y_2606_);
                lean_ctor_set(v___x_2612_, 1, v___x_2611_);
                v___x_2613_ = 0;
                v___x_2614_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2614_, 0, v___x_2612_);
                lean_ctor_set_uint8(
                    v___x_2614_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2613_,
                );
                v___x_2615_ = l_Repr_addAppParen(v___x_2614_, v_prec_2110_);
                return v___x_2615_;
            }
            61 => {
                v___x_2638_ = lean_unsigned_to_nat(1024);
                v___x_2639_ = lean_nat_dec_le(v___x_2638_, v_prec_2110_);
                if v___x_2639_ == 0 {
                    v___x_2640_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2627_ = v___x_2640_;
                    state = 62;
                    continue;
                } else {
                    v___x_2641_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2627_ = v___x_2641_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                v___x_2628_ = l_Lake_instReprCliError_repr___closed__80;
                v___x_2629_ = l_String_quote(v_spec_2622_);
                if v_isShared_2625_ == 0 {
                    lean_ctor_set_tag(v___x_2624_, 3);
                    lean_ctor_set(v___x_2624_, 0, v___x_2629_);
                    v___x_2631_ = v___x_2624_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2637_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2629_);
                    v___x_2631_ = v_reuseFailAlloc_2637_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                v___x_2632_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2632_, 0, v___x_2628_);
                lean_ctor_set(v___x_2632_, 1, v___x_2631_);
                lean_inc(v___y_2627_);
                v___x_2633_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2633_, 0, v___y_2627_);
                lean_ctor_set(v___x_2633_, 1, v___x_2632_);
                v___x_2634_ = 0;
                v___x_2635_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2635_, 0, v___x_2633_);
                lean_ctor_set_uint8(
                    v___x_2635_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2634_,
                );
                v___x_2636_ = l_Repr_addAppParen(v___x_2635_, v_prec_2110_);
                return v___x_2636_;
            }
            64 => {
                v___x_2663_ = lean_unsigned_to_nat(1024);
                v___x_2664_ = lean_nat_dec_le(v___x_2663_, v_prec_2110_);
                if v___x_2664_ == 0 {
                    v___x_2665_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2648_ = v___x_2665_;
                    state = 65;
                    continue;
                } else {
                    v___x_2666_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2648_ = v___x_2666_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                v___x_2649_ = l_Lake_instReprCliError_repr___closed__83;
                v___x_2650_ = lean_unsigned_to_nat(1024);
                v___x_2651_ = l_Lake_instReprCliError_repr___closed__44;
                v___x_2652_ = l_String_quote(v_path_2643_);
                if v_isShared_2646_ == 0 {
                    lean_ctor_set_tag(v___x_2645_, 3);
                    lean_ctor_set(v___x_2645_, 0, v___x_2652_);
                    v___x_2654_ = v___x_2645_;
                    state = 66;
                    continue;
                } else {
                    v_reuseFailAlloc_2662_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2652_);
                    v___x_2654_ = v_reuseFailAlloc_2662_;
                    state = 66;
                    continue;
                }
            }
            66 => {
                v___x_2655_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2655_, 0, v___x_2651_);
                lean_ctor_set(v___x_2655_, 1, v___x_2654_);
                v___x_2656_ = l_Repr_addAppParen(v___x_2655_, v___x_2650_);
                v___x_2657_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2657_, 0, v___x_2649_);
                lean_ctor_set(v___x_2657_, 1, v___x_2656_);
                lean_inc(v___y_2648_);
                v___x_2658_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2658_, 0, v___y_2648_);
                lean_ctor_set(v___x_2658_, 1, v___x_2657_);
                v___x_2659_ = 0;
                v___x_2660_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2660_, 0, v___x_2658_);
                lean_ctor_set_uint8(
                    v___x_2660_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2659_,
                );
                v___x_2661_ = l_Repr_addAppParen(v___x_2660_, v_prec_2110_);
                return v___x_2661_;
            }
            67 => {
                v___x_2698_ = lean_unsigned_to_nat(1024);
                v___x_2699_ = lean_nat_dec_le(v___x_2698_, v_prec_2110_);
                if v___x_2699_ == 0 {
                    v___x_2700_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2682_ = v___x_2700_;
                    state = 68;
                    continue;
                } else {
                    v___x_2701_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2682_ = v___x_2701_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                v___x_2683_ = lean_box(1);
                v___x_2684_ = l_Lake_instReprCliError_repr___closed__86;
                v___x_2685_ = l_String_quote(v_expected_2676_);
                v___x_2686_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2686_, 0, v___x_2685_);
                if v_isShared_2680_ == 0 {
                    lean_ctor_set_tag(v___x_2679_, 5);
                    lean_ctor_set(v___x_2679_, 1, v___x_2686_);
                    lean_ctor_set(v___x_2679_, 0, v___x_2684_);
                    v___x_2688_ = v___x_2679_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2697_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2684_);
                    lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2686_);
                    v___x_2688_ = v_reuseFailAlloc_2697_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_2689_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2689_, 0, v___x_2688_);
                lean_ctor_set(v___x_2689_, 1, v___x_2683_);
                v___x_2690_ = l_String_quote(v_actual_2677_);
                v___x_2691_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2691_, 0, v___x_2690_);
                v___x_2692_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2692_, 0, v___x_2689_);
                lean_ctor_set(v___x_2692_, 1, v___x_2691_);
                lean_inc(v___y_2682_);
                v___x_2693_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2693_, 0, v___y_2682_);
                lean_ctor_set(v___x_2693_, 1, v___x_2692_);
                v___x_2694_ = 0;
                v___x_2695_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2695_, 0, v___x_2693_);
                lean_ctor_set_uint8(
                    v___x_2695_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2694_,
                );
                v___x_2696_ = l_Repr_addAppParen(v___x_2695_, v_prec_2110_);
                return v___x_2696_;
            }
            70 => {
                v___x_2719_ = lean_unsigned_to_nat(1024);
                v___x_2720_ = lean_nat_dec_le(v___x_2719_, v_prec_2110_);
                if v___x_2720_ == 0 {
                    v___x_2721_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2708_ = v___x_2721_;
                    state = 71;
                    continue;
                } else {
                    v___x_2722_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2708_ = v___x_2722_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                v___x_2709_ = l_Lake_instReprCliError_repr___closed__89;
                v___x_2710_ = l_String_quote(v_msg_2703_);
                if v_isShared_2706_ == 0 {
                    lean_ctor_set_tag(v___x_2705_, 3);
                    lean_ctor_set(v___x_2705_, 0, v___x_2710_);
                    v___x_2712_ = v___x_2705_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_2718_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2718_, 0, v___x_2710_);
                    v___x_2712_ = v_reuseFailAlloc_2718_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                v___x_2713_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2713_, 0, v___x_2709_);
                lean_ctor_set(v___x_2713_, 1, v___x_2712_);
                lean_inc(v___y_2708_);
                v___x_2714_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2714_, 0, v___y_2708_);
                lean_ctor_set(v___x_2714_, 1, v___x_2713_);
                v___x_2715_ = 0;
                v___x_2716_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2716_, 0, v___x_2714_);
                lean_ctor_set_uint8(
                    v___x_2716_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2715_,
                );
                v___x_2717_ = l_Repr_addAppParen(v___x_2716_, v_prec_2110_);
                return v___x_2717_;
            }
            73 => {
                v___x_2744_ = lean_unsigned_to_nat(1024);
                v___x_2745_ = lean_nat_dec_le(v___x_2744_, v_prec_2110_);
                if v___x_2745_ == 0 {
                    v___x_2746_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__8_once),
                        _init_l_Lake_instReprCliError_repr___closed__8,
                    );
                    v___y_2729_ = v___x_2746_;
                    state = 74;
                    continue;
                } else {
                    v___x_2747_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9),
                        core::ptr::addr_of_mut!(l_Lake_instReprCliError_repr___closed__9_once),
                        _init_l_Lake_instReprCliError_repr___closed__9,
                    );
                    v___y_2729_ = v___x_2747_;
                    state = 74;
                    continue;
                }
            }
            74 => {
                v___x_2730_ = l_Lake_instReprCliError_repr___closed__92;
                v___x_2731_ = lean_unsigned_to_nat(1024);
                v___x_2732_ = l_Lake_instReprCliError_repr___closed__44;
                v___x_2733_ = l_String_quote(v_path_2724_);
                if v_isShared_2727_ == 0 {
                    lean_ctor_set_tag(v___x_2726_, 3);
                    lean_ctor_set(v___x_2726_, 0, v___x_2733_);
                    v___x_2735_ = v___x_2726_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2733_);
                    v___x_2735_ = v_reuseFailAlloc_2743_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                v___x_2736_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2736_, 0, v___x_2732_);
                lean_ctor_set(v___x_2736_, 1, v___x_2735_);
                v___x_2737_ = l_Repr_addAppParen(v___x_2736_, v___x_2731_);
                v___x_2738_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2738_, 0, v___x_2730_);
                lean_ctor_set(v___x_2738_, 1, v___x_2737_);
                lean_inc(v___y_2729_);
                v___x_2739_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2739_, 0, v___y_2729_);
                lean_ctor_set(v___x_2739_, 1, v___x_2738_);
                v___x_2740_ = 0;
                v___x_2741_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2741_, 0, v___x_2739_);
                lean_ctor_set_uint8(
                    v___x_2741_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2740_,
                );
                v___x_2742_ = l_Repr_addAppParen(v___x_2741_, v_prec_2110_);
                return v___x_2742_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprCliError_repr___boxed(
    mut v_x_2749_: *mut LeanObject,
    mut v_prec_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2751_: *mut LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Lake_instReprCliError_repr(v_x_2749_, v_prec_2750_);
    lean_dec(v_prec_2750_);
    return v_res_2751_;
}
pub unsafe fn l_Nat_cast___at___00List_repr_x27___at___00Lake_instReprCliError_repr_spec__0_spec__1(
    mut v_a_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    v___x_2753_ = lean_nat_to_int(v_a_2752_);
    return v___x_2753_;
}
pub unsafe fn l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(
    mut v_a_2754_: *mut LeanObject,
    mut v_n_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    v___x_2756_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___redArg(v_a_2754_);
    return v___x_2756_;
}
pub unsafe fn l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0___boxed(
    mut v_a_2757_: *mut LeanObject,
    mut v_n_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2759_: *mut LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_List_repr_x27___at___00Lake_instReprCliError_repr_spec__0(v_a_2757_, v_n_2758_);
    lean_dec(v_n_2758_);
    return v_res_2759_;
}
pub unsafe fn l_Lake_CliError_toString(mut v_x_2806_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_2806_) {
        0 => {
            let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
            v___x_2807_ = l_Lake_CliError_toString___closed__0;
            return v___x_2807_;
        }
        1 => {
            let mut v_cmd_2808_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
            v_cmd_2808_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_cmd_2808_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2809_ = l_Lake_CliError_toString___closed__1;
            v___x_2810_ = lean_string_append(v___x_2809_, v_cmd_2808_);
            lean_dec_ref(v_cmd_2808_);
            v___x_2811_ = l_Lake_CliError_toString___closed__2;
            v___x_2812_ = lean_string_append(v___x_2810_, v___x_2811_);
            return v___x_2812_;
        }
        2 => {
            let mut v_arg_2813_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
            v_arg_2813_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_arg_2813_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2814_ = l_Lake_CliError_toString___closed__3;
            v___x_2815_ = lean_string_append(v___x_2814_, v_arg_2813_);
            lean_dec_ref(v_arg_2813_);
            return v___x_2815_;
        }
        3 => {
            let mut v_opt_2816_: *mut LeanObject = core::ptr::null_mut();
            let mut v_arg_2817_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
            v_opt_2816_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_opt_2816_);
            v_arg_2817_ = lean_ctor_get(v_x_2806_, 1);
            lean_inc_ref(v_arg_2817_);
            lean_dec_ref_known(v_x_2806_, 2);
            v___x_2818_ = l_Lake_CliError_toString___closed__3;
            v___x_2819_ = lean_string_append(v___x_2818_, v_arg_2817_);
            lean_dec_ref(v_arg_2817_);
            v___x_2820_ = l_Lake_CliError_toString___closed__4;
            v___x_2821_ = lean_string_append(v___x_2819_, v___x_2820_);
            v___x_2822_ = lean_string_append(v___x_2821_, v_opt_2816_);
            lean_dec_ref(v_opt_2816_);
            return v___x_2822_;
        }
        4 => {
            let mut v_opt_2823_: *mut LeanObject = core::ptr::null_mut();
            let mut v_arg_2824_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
            v_opt_2823_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_opt_2823_);
            v_arg_2824_ = lean_ctor_get(v_x_2806_, 1);
            lean_inc_ref(v_arg_2824_);
            lean_dec_ref_known(v_x_2806_, 2);
            v___x_2825_ = l_Lake_CliError_toString___closed__5;
            v___x_2826_ = lean_string_append(v___x_2825_, v_opt_2823_);
            lean_dec_ref(v_opt_2823_);
            v___x_2827_ = l_Lake_CliError_toString___closed__6;
            v___x_2828_ = lean_string_append(v___x_2826_, v___x_2827_);
            v___x_2829_ = lean_string_append(v___x_2828_, v_arg_2824_);
            lean_dec_ref(v_arg_2824_);
            return v___x_2829_;
        }
        5 => {
            let mut v_opt_2830_: u32 = 0;
            let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
            v_opt_2830_ = lean_ctor_get_uint32(v_x_2806_, 0 as u32);
            lean_dec_ref_known(v_x_2806_, 0);
            v___x_2831_ = l_Lake_CliError_toString___closed__7;
            v___x_2832_ = l_Lake_CliError_toString___closed__8;
            v___x_2833_ = lean_string_push(v___x_2832_, v_opt_2830_);
            v___x_2834_ = lean_string_append(v___x_2831_, v___x_2833_);
            lean_dec_ref(v___x_2833_);
            v___x_2835_ = l_Lake_CliError_toString___closed__2;
            v___x_2836_ = lean_string_append(v___x_2834_, v___x_2835_);
            return v___x_2836_;
        }
        6 => {
            let mut v_opt_2837_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
            v_opt_2837_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_opt_2837_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2838_ = l_Lake_CliError_toString___closed__9;
            v___x_2839_ = lean_string_append(v___x_2838_, v_opt_2837_);
            lean_dec_ref(v_opt_2837_);
            v___x_2840_ = l_Lake_CliError_toString___closed__2;
            v___x_2841_ = lean_string_append(v___x_2839_, v___x_2840_);
            return v___x_2841_;
        }
        7 => {
            let mut v_args_2842_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
            v_args_2842_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc(v_args_2842_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2843_ = l_Lake_CliError_toString___closed__10;
            v___x_2844_ = l_Lake_CliError_toString___closed__11;
            v___x_2845_ = l_String_intercalate(v___x_2844_, v_args_2842_);
            v___x_2846_ = lean_string_append(v___x_2843_, v___x_2845_);
            lean_dec_ref(v___x_2845_);
            return v___x_2846_;
        }
        8 => {
            let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
            v___x_2847_ = l_Lake_CliError_toString___closed__12;
            return v___x_2847_;
        }
        9 => {
            let mut v_spec_2848_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
            v_spec_2848_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_spec_2848_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2849_ = l_Lake_CliError_toString___closed__13;
            v___x_2850_ = lean_string_append(v___x_2849_, v_spec_2848_);
            lean_dec_ref(v_spec_2848_);
            v___x_2851_ = l_Lake_CliError_toString___closed__14;
            v___x_2852_ = lean_string_append(v___x_2850_, v___x_2851_);
            return v___x_2852_;
        }
        10 => {
            let mut v_spec_2853_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
            v_spec_2853_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_spec_2853_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2854_ = l_Lake_CliError_toString___closed__15;
            v___x_2855_ = lean_string_append(v___x_2854_, v_spec_2853_);
            lean_dec_ref(v_spec_2853_);
            v___x_2856_ = l_Lake_CliError_toString___closed__14;
            v___x_2857_ = lean_string_append(v___x_2855_, v___x_2856_);
            return v___x_2857_;
        }
        11 => {
            let mut v_mod_2858_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2860_: u8 = 0;
            let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
            v_mod_2858_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc(v_mod_2858_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2859_ = l_Lake_CliError_toString___closed__16;
            v___x_2860_ = 0;
            v___x_2861_ = l_Lean_Name_toString(v_mod_2858_, v___x_2860_);
            v___x_2862_ = lean_string_append(v___x_2859_, v___x_2861_);
            lean_dec_ref(v___x_2861_);
            v___x_2863_ = l_Lake_CliError_toString___closed__14;
            v___x_2864_ = lean_string_append(v___x_2862_, v___x_2863_);
            return v___x_2864_;
        }
        12 => {
            let mut v_path_2865_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
            v_path_2865_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_path_2865_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2866_ = l_Lake_CliError_toString___closed__17;
            v___x_2867_ = lean_string_append(v___x_2866_, v_path_2865_);
            lean_dec_ref(v_path_2865_);
            v___x_2868_ = l_Lake_CliError_toString___closed__14;
            v___x_2869_ = lean_string_append(v___x_2867_, v___x_2868_);
            return v___x_2869_;
        }
        13 => {
            let mut v_spec_2870_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
            v_spec_2870_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_spec_2870_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2871_ = l_Lake_CliError_toString___closed__18;
            v___x_2872_ = lean_string_append(v___x_2871_, v_spec_2870_);
            lean_dec_ref(v_spec_2870_);
            v___x_2873_ = l_Lake_CliError_toString___closed__14;
            v___x_2874_ = lean_string_append(v___x_2872_, v___x_2873_);
            return v___x_2874_;
        }
        14 => {
            let mut v_type_2875_: *mut LeanObject = core::ptr::null_mut();
            let mut v_facet_2876_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2881_: u8 = 0;
            let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
            v_type_2875_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_type_2875_);
            v_facet_2876_ = lean_ctor_get(v_x_2806_, 1);
            lean_inc(v_facet_2876_);
            lean_dec_ref_known(v_x_2806_, 2);
            v___x_2877_ = l_Lake_CliError_toString___closed__19;
            v___x_2878_ = lean_string_append(v___x_2877_, v_type_2875_);
            lean_dec_ref(v_type_2875_);
            v___x_2879_ = l_Lake_CliError_toString___closed__20;
            v___x_2880_ = lean_string_append(v___x_2878_, v___x_2879_);
            v___x_2881_ = 0;
            v___x_2882_ = l_Lean_Name_toString(v_facet_2876_, v___x_2881_);
            v___x_2883_ = lean_string_append(v___x_2880_, v___x_2882_);
            lean_dec_ref(v___x_2882_);
            v___x_2884_ = l_Lake_CliError_toString___closed__14;
            v___x_2885_ = lean_string_append(v___x_2883_, v___x_2884_);
            return v___x_2885_;
        }
        15 => {
            let mut v_target_2886_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2888_: u8 = 0;
            let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
            v_target_2886_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc(v_target_2886_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2887_ = l_Lake_CliError_toString___closed__21;
            v___x_2888_ = 0;
            v___x_2889_ = l_Lean_Name_toString(v_target_2886_, v___x_2888_);
            v___x_2890_ = lean_string_append(v___x_2887_, v___x_2889_);
            lean_dec_ref(v___x_2889_);
            v___x_2891_ = l_Lake_CliError_toString___closed__14;
            v___x_2892_ = lean_string_append(v___x_2890_, v___x_2891_);
            return v___x_2892_;
        }
        16 => {
            let mut v_pkg_2893_: *mut LeanObject = core::ptr::null_mut();
            let mut v_mod_2894_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2896_: u8 = 0;
            let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
            v_pkg_2893_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc(v_pkg_2893_);
            v_mod_2894_ = lean_ctor_get(v_x_2806_, 1);
            lean_inc(v_mod_2894_);
            lean_dec_ref_known(v_x_2806_, 2);
            v___x_2895_ = l_Lake_CliError_toString___closed__22;
            v___x_2896_ = 0;
            v___x_2897_ = l_Lean_Name_toString(v_pkg_2893_, v___x_2896_);
            v___x_2898_ = lean_string_append(v___x_2895_, v___x_2897_);
            lean_dec_ref(v___x_2897_);
            v___x_2899_ = l_Lake_CliError_toString___closed__23;
            v___x_2900_ = lean_string_append(v___x_2898_, v___x_2899_);
            v___x_2901_ = l_Lean_Name_toString(v_mod_2894_, v___x_2896_);
            v___x_2902_ = lean_string_append(v___x_2900_, v___x_2901_);
            lean_dec_ref(v___x_2901_);
            v___x_2903_ = l_Lake_CliError_toString___closed__2;
            v___x_2904_ = lean_string_append(v___x_2902_, v___x_2903_);
            return v___x_2904_;
        }
        17 => {
            let mut v_pkg_2905_: *mut LeanObject = core::ptr::null_mut();
            let mut v_spec_2906_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2908_: u8 = 0;
            let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
            v_pkg_2905_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc(v_pkg_2905_);
            v_spec_2906_ = lean_ctor_get(v_x_2806_, 1);
            lean_inc_ref(v_spec_2906_);
            lean_dec_ref_known(v_x_2806_, 2);
            v___x_2907_ = l_Lake_CliError_toString___closed__22;
            v___x_2908_ = 0;
            v___x_2909_ = l_Lean_Name_toString(v_pkg_2905_, v___x_2908_);
            v___x_2910_ = lean_string_append(v___x_2907_, v___x_2909_);
            lean_dec_ref(v___x_2909_);
            v___x_2911_ = l_Lake_CliError_toString___closed__24;
            v___x_2912_ = lean_string_append(v___x_2910_, v___x_2911_);
            v___x_2913_ = lean_string_append(v___x_2912_, v_spec_2906_);
            lean_dec_ref(v_spec_2906_);
            v___x_2914_ = l_Lake_CliError_toString___closed__2;
            v___x_2915_ = lean_string_append(v___x_2913_, v___x_2914_);
            return v___x_2915_;
        }
        18 => {
            let mut v_key_2916_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
            v_key_2916_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_key_2916_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2917_ = l_Lake_CliError_toString___closed__2;
            v___x_2918_ = lean_string_append(v___x_2917_, v_key_2916_);
            lean_dec_ref(v_key_2916_);
            v___x_2919_ = l_Lake_CliError_toString___closed__25;
            v___x_2920_ = lean_string_append(v___x_2918_, v___x_2919_);
            return v___x_2920_;
        }
        19 => {
            let mut v_spec_2921_: *mut LeanObject = core::ptr::null_mut();
            let mut v_tooMany_2922_: u32 = 0;
            let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
            v_spec_2921_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_spec_2921_);
            v_tooMany_2922_ = lean_ctor_get_uint32(
                v_x_2806_,
                (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            );
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2923_ = l_Lake_CliError_toString___closed__26;
            v___x_2924_ = lean_string_append(v___x_2923_, v_spec_2921_);
            lean_dec_ref(v_spec_2921_);
            v___x_2925_ = l_Lake_CliError_toString___closed__27;
            v___x_2926_ = lean_string_append(v___x_2924_, v___x_2925_);
            v___x_2927_ = l_Lake_CliError_toString___closed__8;
            v___x_2928_ = lean_string_push(v___x_2927_, v_tooMany_2922_);
            v___x_2929_ = lean_string_append(v___x_2926_, v___x_2928_);
            lean_dec_ref(v___x_2928_);
            v___x_2930_ = l_Lake_CliError_toString___closed__28;
            v___x_2931_ = lean_string_append(v___x_2929_, v___x_2930_);
            return v___x_2931_;
        }
        20 => {
            let mut v_target_2932_: *mut LeanObject = core::ptr::null_mut();
            let mut v_facet_2933_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2935_: u8 = 0;
            let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
            v_target_2932_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc(v_target_2932_);
            v_facet_2933_ = lean_ctor_get(v_x_2806_, 1);
            lean_inc(v_facet_2933_);
            lean_dec_ref_known(v_x_2806_, 2);
            v___x_2934_ = l_Lake_CliError_toString___closed__29;
            v___x_2935_ = 0;
            v___x_2936_ = l_Lean_Name_toString(v_facet_2933_, v___x_2935_);
            v___x_2937_ = lean_string_append(v___x_2934_, v___x_2936_);
            lean_dec_ref(v___x_2936_);
            v___x_2938_ = l_Lake_CliError_toString___closed__30;
            v___x_2939_ = lean_string_append(v___x_2937_, v___x_2938_);
            v___x_2940_ = l_Lean_Name_toString(v_target_2932_, v___x_2935_);
            v___x_2941_ = lean_string_append(v___x_2939_, v___x_2940_);
            lean_dec_ref(v___x_2940_);
            v___x_2942_ = l_Lake_CliError_toString___closed__31;
            v___x_2943_ = lean_string_append(v___x_2941_, v___x_2942_);
            return v___x_2943_;
        }
        21 => {
            let mut v_spec_2944_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
            v_spec_2944_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_spec_2944_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2945_ = l_Lake_CliError_toString___closed__32;
            v___x_2946_ = lean_string_append(v___x_2945_, v_spec_2944_);
            lean_dec_ref(v_spec_2944_);
            return v___x_2946_;
        }
        22 => {
            let mut v_script_2947_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
            v_script_2947_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_script_2947_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2948_ = l_Lake_CliError_toString___closed__33;
            v___x_2949_ = lean_string_append(v___x_2948_, v_script_2947_);
            lean_dec_ref(v_script_2947_);
            return v___x_2949_;
        }
        23 => {
            let mut v_script_2950_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
            v_script_2950_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_script_2950_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2951_ = l_Lake_CliError_toString___closed__34;
            v___x_2952_ = lean_string_append(v___x_2951_, v_script_2950_);
            lean_dec_ref(v_script_2950_);
            v___x_2953_ = l_Lake_CliError_toString___closed__14;
            v___x_2954_ = lean_string_append(v___x_2952_, v___x_2953_);
            return v___x_2954_;
        }
        24 => {
            let mut v_spec_2955_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
            v_spec_2955_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_spec_2955_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2956_ = l_Lake_CliError_toString___closed__35;
            v___x_2957_ = lean_string_append(v___x_2956_, v_spec_2955_);
            lean_dec_ref(v_spec_2955_);
            v___x_2958_ = l_Lake_CliError_toString___closed__36;
            v___x_2959_ = lean_string_append(v___x_2957_, v___x_2958_);
            return v___x_2959_;
        }
        25 => {
            let mut v_path_2960_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
            v_path_2960_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_path_2960_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2961_ = l_Lake_CliError_toString___closed__37;
            v___x_2962_ = lean_string_append(v___x_2961_, v_path_2960_);
            lean_dec_ref(v_path_2960_);
            return v___x_2962_;
        }
        26 => {
            let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
            v___x_2963_ = l_Lake_CliError_toString___closed__38;
            return v___x_2963_;
        }
        27 => {
            let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
            v___x_2964_ = l_Lake_CliError_toString___closed__39;
            return v___x_2964_;
        }
        28 => {
            let mut v_expected_2965_: *mut LeanObject = core::ptr::null_mut();
            let mut v_actual_2966_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2973_: u8 = 0;
            v_expected_2965_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_expected_2965_);
            v_actual_2966_ = lean_ctor_get(v_x_2806_, 1);
            lean_inc_ref(v_actual_2966_);
            lean_dec_ref_known(v_x_2806_, 2);
            v___x_2967_ = l_Lake_CliError_toString___closed__40;
            v___x_2968_ = lean_string_append(v___x_2967_, v_expected_2965_);
            lean_dec_ref(v_expected_2965_);
            v___x_2969_ = l_Lake_CliError_toString___closed__41;
            v___x_2970_ = lean_string_append(v___x_2968_, v___x_2969_);
            v___x_2971_ = lean_string_utf8_byte_size(v_actual_2966_);
            v___x_2972_ = lean_unsigned_to_nat(0);
            v___x_2973_ = lean_nat_dec_eq(v___x_2971_, v___x_2972_);
            if v___x_2973_ == 0 {
                let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
                v___x_2974_ = lean_string_append(v___x_2970_, v_actual_2966_);
                lean_dec_ref(v_actual_2966_);
                return v___x_2974_;
            } else {
                let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v_actual_2966_);
                v___x_2975_ = l_Lake_CliError_toString___closed__42;
                v___x_2976_ = lean_string_append(v___x_2970_, v___x_2975_);
                return v___x_2976_;
            }
        }
        29 => {
            let mut v_msg_2977_: *mut LeanObject = core::ptr::null_mut();
            v_msg_2977_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_msg_2977_);
            lean_dec_ref_known(v_x_2806_, 1);
            return v_msg_2977_;
        }
        _ => {
            let mut v_path_2978_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
            v_path_2978_ = lean_ctor_get(v_x_2806_, 0);
            lean_inc_ref(v_path_2978_);
            lean_dec_ref_known(v_x_2806_, 1);
            v___x_2979_ = l_Lake_CliError_toString___closed__43;
            v___x_2980_ = lean_string_append(v___x_2979_, v_path_2978_);
            lean_dec_ref(v_path_2978_);
            return v___x_2980_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_instInhabitedCliError_default = _init_l_Lake_instInhabitedCliError_default();
    lean_mark_persistent(l_Lake_instInhabitedCliError_default);
    l_Lake_instInhabitedCliError = _init_l_Lake_instInhabitedCliError();
    lean_mark_persistent(l_Lake_instInhabitedCliError);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI_Error(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_System_FilePath(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_CLI_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_CLI_Error(builtin);
}
