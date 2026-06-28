// Lean compiler output
// Module: Lake.Util.Version
// Imports: Lean.Data.Json Lake.Util.Date Init.Control.Do Init.Data.String.TakeDrop Lean.Data.Trie Init.Data.String.Search Init.Omega Init.Data.String.Length
use crate::r#gen::Init::Control::Do::{
    initialize_Init_Control_Do, runtime_initialize_Init_Control_Do,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Option::Basic::l_Option_instDecidableEq___redArg;
use crate::r#gen::Init::Data::Repr::{
    l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen, l_String_quote,
};
use crate::r#gen::Init::Data::String::Basic::{
    l_String_Slice_Pos_get_x3f, l_String_Slice_Pos_nextn, l_String_Slice_pos_x21, l_String_decLE,
};
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    l_String_Slice_beq, l_String_Slice_toNat_x3f, l_String_Slice_toString, l_String_Slice_trimAscii,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_instDecidableEqNat___boxed;
use crate::r#gen::Init::System::FilePath::l_System_FilePath_join;
use crate::r#gen::Init::System::IO::l_IO_FS_readFile;
use crate::r#gen::Lake::Util::Date::{
    initialize_Lake_Util_Date, l_Lake_Date_ofString_x3f, l_Lake_Date_toString,
    l_Lake_instDecidableEqDate_decEq, l_Lake_instOrdDate_ord, l_Lake_instReprDate_repr___redArg,
    runtime_initialize_Lake_Util_Date,
};
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_getStr_x3f;
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
use crate::r#gen::Lean::Data::Trie::{
    initialize_Lean_Data_Trie, l_Lean_Data_Trie_empty, l_Lean_Data_Trie_insert___redArg,
    l_Lean_Data_Trie_matchPrefix___redArg, runtime_initialize_Lean_Data_Trie,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::Ord::String::lean_string_compare;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_dec_lt, lean_string_is_valid_pos, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_uint32, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0_value:
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
static mut l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0_value:
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
    m_data: [105, 110, 118, 97, 108, 105, 100, 32, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1_value:
    LeanStringObject<34> = LeanStringObject {
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
        32, 118, 101, 114, 115, 105, 111, 110, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32,
        110, 117, 109, 101, 114, 97, 108, 44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2_value:
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
    m_data: [39, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        32, 118, 101, 114, 115, 105, 111, 110, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32,
        110, 117, 109, 101, 114, 97, 108, 32, 111, 114, 32, 119, 105, 108, 100, 99, 97, 114, 100,
        44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0_value:
    LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 118, 101, 114, 115, 105, 111, 110, 58, 32, 39, 45,
        39, 32, 115, 117, 102, 102, 105, 120, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101,
        109, 112, 116, 121, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value:
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
static mut l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0_value:
    LeanStringObject<42> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 104, 97, 114, 97, 99, 116, 101,
        114, 115, 32, 97, 116, 32, 101, 110, 100, 32, 111, 102, 32, 118, 101, 114, 115, 105, 111,
        110, 58, 32, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0_value
)
    as *mut LeanObject;
pub static l_Lake_instInhabitedSemVerCore_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedSemVerCore_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedSemVerCore_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedSemVerCore_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedSemVerCore_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lake_instInhabitedSemVerCore: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedSemVerCore_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [109, 97, 106, 111, 114, 0],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__8_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__10_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [109, 105, 110, 111, 114, 0],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__12_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [112, 97, 116, 99, 104, 0],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__13_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__13_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__14_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__14_value)
        as *mut LeanObject;
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__17_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore_repr___redArg___closed__18_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__14_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprSemVerCore_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lake_instReprSemVerCore___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprSemVerCore_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprSemVerCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprSemVerCore: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprSemVerCore___closed__0_value) as *mut LeanObject;
pub static l_Lake_instOrdSemVerCore___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instOrdSemVerCore_ord___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instOrdSemVerCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdSemVerCore___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instOrdSemVerCore: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instOrdSemVerCore___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_SemVerCore_instLT: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_SemVerCore_instLE: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_SemVerCore_instMin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_SemVerCore_instMin___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_SemVerCore_instMin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instMin___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_SemVerCore_instMin: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instMin___closed__0_value) as *mut LeanObject;
pub static l_Lake_SemVerCore_instMax___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_SemVerCore_instMax___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_SemVerCore_instMax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_SemVerCore_instMax: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instMax___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0_value:
    LeanStringObject<23> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32, 99, 111, 114,
        101, 58, 32, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1_value:
    LeanStringObject<37> = LeanStringObject {
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
        105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102,
        32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 58, 32, 103, 111, 116, 32, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 51, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3_value:
    LeanStringObject<47> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 112, 97, 116, 99, 104, 32, 118, 101, 114, 115, 105,
        111, 110, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 101, 114, 97,
        108, 44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4_value:
    LeanStringObject<47> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 109, 105, 110, 111, 114, 32, 118, 101, 114, 115, 105,
        111, 110, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 101, 114, 97,
        108, 44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5_value:
    LeanStringObject<47> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 109, 97, 106, 111, 114, 32, 118, 101, 114, 115, 105,
        111, 110, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 110, 117, 109, 101, 114, 97,
        108, 44, 32, 103, 111, 116, 32, 39, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_SemVerCore_toString___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lake_SemVerCore_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_toString___closed__0_value) as *mut LeanObject;
pub static l_Lake_SemVerCore_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_SemVerCore_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_SemVerCore_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_SemVerCore_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_SemVerCore_instToJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_SemVerCore_instToJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_SemVerCore_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_SemVerCore_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instToJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_SemVerCore_instFromJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_SemVerCore_instFromJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_SemVerCore_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_SemVerCore_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_SemVerCore_instFromJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedStdVer_default___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_instInhabitedSemVerCore_default___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedStdVer_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStdVer_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedStdVer_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStdVer_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedStdVer: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedStdVer_default___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprStdVer_repr___redArg___closed__0_value: LeanStringObject<13> =
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
        m_data: [116, 111, 83, 101, 109, 86, 101, 114, 67, 111, 114, 101, 0],
    };
static mut l_Lake_instReprStdVer_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprStdVer_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprStdVer_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprStdVer_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprStdVer_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprStdVer_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprStdVer_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__3_value) as *mut LeanObject;
static mut l_Lake_instReprStdVer_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprStdVer_repr___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprStdVer_repr___redArg___closed__5_value: LeanStringObject<13> =
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
        m_data: [115, 112, 101, 99, 105, 97, 108, 68, 101, 115, 99, 114, 0],
    };
static mut l_Lake_instReprStdVer_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprStdVer_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprStdVer_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer_repr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprStdVer___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprStdVer_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprStdVer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprStdVer: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprStdVer___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_instCoeSemVerCore___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_StdVer_instCoeSemVerCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instCoeSemVerCore___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instCoeSemVerCore: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instCoeSemVerCore___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_StdVer_ofSemVerCore as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_StdVer_instCoeSemVerCore__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instCoeSemVerCore__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instCoeSemVerCore__1___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_instOrd___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_StdVer_compare___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_StdVer_instOrd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instOrd___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instOrd: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instOrd___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instLT: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_StdVer_instLE: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_StdVer_instMin___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_StdVer_instMin___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_StdVer_instMin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instMin___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instMin: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instMin___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_instMax___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_StdVer_instMax___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_StdVer_instMax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instMax___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instMax: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instMax___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_toString___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l_Lake_StdVer_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_toString___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_StdVer_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_StdVer_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_instToJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_StdVer_instToJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_StdVer_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instToJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_StdVer_instFromJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_StdVer_instFromJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_StdVer_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_StdVer_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_StdVer_instFromJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_toolchainFileName___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        108, 101, 97, 110, 45, 116, 111, 111, 108, 99, 104, 97, 105, 110, 0,
    ],
};
static mut l_Lake_toolchainFileName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_toolchainFileName___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_toolchainFileName: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_toolchainFileName___closed__0_value) as *mut LeanObject;
pub static l_Lake_ToolchainVer_defaultOrigin___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
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
            108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 108, 101, 97, 110, 52, 0,
        ],
    };
static mut l_Lake_ToolchainVer_defaultOrigin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_defaultOrigin___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ToolchainVer_defaultOrigin: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_defaultOrigin___closed__0_value) as *mut LeanObject;
pub static l_Lake_ToolchainVer_prOrigin___closed__0_value: LeanStringObject<29> =
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
            108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 108, 101, 97, 110, 52, 45, 112,
            114, 45, 114, 101, 108, 101, 97, 115, 101, 115, 0,
        ],
    };
static mut l_Lake_ToolchainVer_prOrigin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_prOrigin___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ToolchainVer_prOrigin: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_prOrigin___closed__0_value) as *mut LeanObject;
pub static l_Lake_ToolchainVer_release___override___closed__0_value: LeanStringObject<19> =
    LeanStringObject {
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
            108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 108, 101, 97, 110, 52, 58, 118, 0,
        ],
    };
static mut l_Lake_ToolchainVer_release___override___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_release___override___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_ToolchainVer_nightly___override___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 108, 101, 97, 110, 52, 58, 110,
            105, 103, 104, 116, 108, 121, 45, 0,
        ],
    };
static mut l_Lake_ToolchainVer_nightly___override___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_nightly___override___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_ToolchainVer_nightly___override___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [45, 114, 101, 118, 0],
    };
static mut l_Lake_ToolchainVer_nightly___override___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_nightly___override___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_ToolchainVer_pr___override___closed__0_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            108, 101, 97, 110, 112, 114, 111, 118, 101, 114, 47, 108, 101, 97, 110, 52, 45, 112,
            114, 45, 114, 101, 108, 101, 97, 115, 101, 115, 58, 112, 114, 45, 114, 101, 108, 101,
            97, 115, 101, 45, 0,
        ],
    };
static mut l_Lake_ToolchainVer_pr___override___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_pr___override___closed__0_value) as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value:
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
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1_value:
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
        l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value:
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
    m_data: [115, 111, 109, 101, 32, 0],
};
static mut l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value
) as *mut LeanObject;
pub static l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3_value:
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
        l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__2_value
    ) as *mut LeanObject],
};
static mut l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3_value
) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 97, 107, 101, 46, 84, 111, 111, 108, 99, 104, 97, 105, 110, 86, 101, 114, 46, 114,
            101, 108, 101, 97, 115, 101, 0,
        ],
    };
static mut l_Lake_instReprToolchainVer_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprToolchainVer_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__1_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprToolchainVer_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__2_value) as *mut LeanObject;
static mut l_Lake_instReprToolchainVer_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprToolchainVer_repr___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_instReprToolchainVer_repr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprToolchainVer_repr___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instReprToolchainVer_repr___closed__5_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 97, 107, 101, 46, 84, 111, 111, 108, 99, 104, 97, 105, 110, 86, 101, 114, 46, 110,
            105, 103, 104, 116, 108, 121, 0,
        ],
    };
static mut l_Lake_instReprToolchainVer_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprToolchainVer_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__6_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprToolchainVer_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__7_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__8_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 84, 111, 111, 108, 99, 104, 97, 105, 110, 86, 101, 114, 46, 112,
            114, 0,
        ],
    };
static mut l_Lake_instReprToolchainVer_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__8_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprToolchainVer_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__9_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__10_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__9_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprToolchainVer_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__10_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__11_value: LeanStringObject<24> =
    LeanStringObject {
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
            76, 97, 107, 101, 46, 84, 111, 111, 108, 99, 104, 97, 105, 110, 86, 101, 114, 46, 111,
            116, 104, 101, 114, 0,
        ],
    };
static mut l_Lake_instReprToolchainVer_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__11_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprToolchainVer_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__12_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer_repr___closed__13_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__12_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprToolchainVer_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer_repr___closed__13_value) as *mut LeanObject;
pub static l_Lake_instReprToolchainVer___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprToolchainVer_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprToolchainVer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprToolchainVer: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprToolchainVer___closed__0_value) as *mut LeanObject;
pub static l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ToolchainVer_release___override as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ToolchainVer_instCoeLeanVer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ToolchainVer_instCoeLeanVer: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instCoeLeanVer___closed__0_value) as *mut LeanObject;
pub static l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 105, 103, 104, 116, 108, 121, 45, 0]};
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 114, 45, 114, 101, 108, 101, 97, 115, 101, 45, 0]};
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_ToolchainVer_ofString___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [45, 110, 105, 103, 104, 116, 108, 121, 0],
};
static mut l_Lake_ToolchainVer_ofString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_ofString___closed__0_value) as *mut LeanObject;
static mut l_Lake_ToolchainVer_ofString___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_ToolchainVer_ofString___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lake_ToolchainVer_ofString___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_ToolchainVer_ofString___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_ToolchainVer_ofString___closed__3_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [118, 0],
};
static mut l_Lake_ToolchainVer_ofString___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_ofString___closed__3_value) as *mut LeanObject;
static mut l_Lake_ToolchainVer_ofString___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_ToolchainVer_ofString___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_ToolchainVer_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ToolchainVer_toString___override___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ToolchainVer_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ToolchainVer_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_ToolchainVer_instToJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ToolchainVer_instToJson___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ToolchainVer_instToJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instToJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ToolchainVer_instToJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instToJson___closed__0_value) as *mut LeanObject;
pub static l_Lake_ToolchainVer_instFromJson___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ToolchainVer_instFromJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ToolchainVer_instFromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ToolchainVer_instFromJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ToolchainVer_instFromJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ToolchainVer_instLT: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_ToolchainVer_instLE: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_instDecodeVersionSemVerCore___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_SemVerCore_parse as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instDecodeVersionSemVerCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDecodeVersionSemVerCore___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instDecodeVersionSemVerCore: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDecodeVersionSemVerCore___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDecodeVersionStdVer___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_StdVer_parse as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instDecodeVersionStdVer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDecodeVersionStdVer___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instDecodeVersionStdVer: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDecodeVersionStdVer___closed__0_value) as *mut LeanObject;
pub static l_Lake_instDecodeVersionToolchainVer___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instDecodeVersionToolchainVer___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instDecodeVersionToolchainVer___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDecodeVersionToolchainVer___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instDecodeVersionToolchainVer: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instDecodeVersionToolchainVer___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__0_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 109, 112, 97, 114, 97, 116, 111, 114, 79, 112, 46, 108,
            116, 0,
        ],
    };
static mut l_Lake_instReprComparatorOp_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprComparatorOp_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__2_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 109, 112, 97, 114, 97, 116, 111, 114, 79, 112, 46, 108,
            101, 0,
        ],
    };
static mut l_Lake_instReprComparatorOp_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprComparatorOp_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__3_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__4_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 109, 112, 97, 114, 97, 116, 111, 114, 79, 112, 46, 103,
            116, 0,
        ],
    };
static mut l_Lake_instReprComparatorOp_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__4_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprComparatorOp_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__6_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 109, 112, 97, 114, 97, 116, 111, 114, 79, 112, 46, 103,
            101, 0,
        ],
    };
static mut l_Lake_instReprComparatorOp_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__6_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__7_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprComparatorOp_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__7_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__8_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 109, 112, 97, 114, 97, 116, 111, 114, 79, 112, 46, 101,
            113, 0,
        ],
    };
static mut l_Lake_instReprComparatorOp_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__8_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lake_instReprComparatorOp_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__9_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__10_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 97, 107, 101, 46, 67, 111, 109, 112, 97, 114, 97, 116, 111, 114, 79, 112, 46, 110,
            101, 0,
        ],
    };
static mut l_Lake_instReprComparatorOp_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__10_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp_repr___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprComparatorOp_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp_repr___closed__11_value) as *mut LeanObject;
pub static l_Lake_instReprComparatorOp___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprComparatorOp_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprComparatorOp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprComparatorOp: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprComparatorOp___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedComparatorOp_default: u8 = 0;
pub static mut l_Lake_instInhabitedComparatorOp: u8 = 0;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 137, 160, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1_value:
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
    m_data: [33, 61, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2_value:
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
    m_data: [61, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 137, 165, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4_value:
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
    m_data: [62, 61, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5_value:
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
    m_data: [62, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 137, 164, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7_value:
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
    m_data: [60, 61, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8_value:
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
    m_data: [60, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8_value
) as *mut LeanObject;
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0_value:
    LeanStringObject<63> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 63,
    m_capacity: 63,
    m_length: 62,
    m_data: [
        40, 105, 110, 116, 101, 114, 110, 97, 108, 41, 32, 99, 111, 109, 112, 97, 114, 105, 115,
        111, 110, 32, 111, 112, 101, 114, 97, 116, 111, 114, 32, 112, 97, 114, 115, 101, 32, 112,
        114, 111, 100, 117, 99, 101, 100, 32, 105, 110, 118, 97, 108, 105, 100, 32, 112, 111, 115,
        105, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1_value:
    LeanStringObject<29> = LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 109, 112, 97, 114, 105, 115, 111, 110,
        32, 111, 112, 101, 114, 97, 116, 111, 114, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_ComparatorOp_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ComparatorOp_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ComparatorOp_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ComparatorOp_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_ComparatorOp_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ComparatorOp_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprVerComparator_repr___redArg___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [118, 101, 114, 0],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_instReprVerComparator_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_instReprVerComparator_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_instReprVerComparator_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lake_instReprVerComparator_repr___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprVerComparator_repr___redArg___closed__5_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [111, 112, 0],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_instReprVerComparator_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lake_instReprVerComparator_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprVerComparator_repr___redArg___closed__8_value: LeanStringObject<16> =
    LeanStringObject {
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
            105, 110, 99, 108, 117, 100, 101, 83, 117, 102, 102, 105, 120, 101, 115, 0,
        ],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_instReprVerComparator_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator_repr___redArg___closed__9_value)
        as *mut LeanObject;
static mut l_Lake_instReprVerComparator_repr___redArg___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprVerComparator_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprVerComparator___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprVerComparator_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprVerComparator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprVerComparator: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerComparator___closed__0_value) as *mut LeanObject;
pub static l_Lake_VerComparator_wild___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_instInhabitedSemVerCore_default___closed__0_value)
            as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Lake_VerComparator_wild___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerComparator_wild___closed__0_value) as *mut LeanObject;
pub static l_Lake_VerComparator_wild___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_VerComparator_wild___closed__0_value) as *mut LeanObject,
        3 as *mut LeanObject,
    ],
};
static mut l_Lake_VerComparator_wild___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerComparator_wild___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_VerComparator_wild: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerComparator_wild___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_VerComparator_instInhabited: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerComparator_wild___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0_value:
    LeanStringObject<45> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 99, 111, 109, 112, 97, 114, 105, 115, 111, 110, 58,
        32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32, 97,
        102, 116, 101, 114, 32, 96, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1_value:
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
    m_data: [96, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1_value
)
    as *mut LeanObject;
pub static l_Lake_VerComparator_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_VerComparator_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_VerComparator_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerComparator_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_VerComparator_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerComparator_instToString___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [35, 91, 0]};
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__9_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value) as *mut LeanObject;
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5_value) as *mut LeanObject;
pub static l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__2_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6_value) as *mut LeanObject;
pub static l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [35, 91, 93, 0]};
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value) as *mut LeanObject;
pub static l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__7_value) as *mut LeanObject] };
static mut l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8_value) as *mut LeanObject;
pub static l_Lake_instReprVerRange_repr___redArg___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [116, 111, 83, 116, 114, 105, 110, 103, 0],
    };
static mut l_Lake_instReprVerRange_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_instReprVerRange_repr___redArg___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerRange_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lake_instReprVerRange_repr___redArg___closed__2_value: LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerRange_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lake_instReprVerRange_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instReprSemVerCore_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerRange_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__3_value) as *mut LeanObject;
static mut l_Lake_instReprVerRange_repr___redArg___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprVerRange_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprVerRange_repr___redArg___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [99, 108, 97, 117, 115, 101, 115, 0],
    };
static mut l_Lake_instReprVerRange_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lake_instReprVerRange_repr___redArg___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instReprVerRange_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange_repr___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lake_instReprVerRange_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_instReprVerRange_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprVerRange___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_instReprVerRange_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_instReprVerRange___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_instReprVerRange: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instReprVerRange___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedVerRange_default___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lake_instInhabitedVerRange_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedVerRange_default___closed__0_value) as *mut LeanObject;
pub static l_Lake_instInhabitedVerRange_default___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(
                l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1_value
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lake_instInhabitedVerRange_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_instInhabitedVerRange_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedVerRange_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedVerRange_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedVerRange_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lake_instInhabitedVerRange: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedVerRange_default___closed__1_value) as *mut LeanObject;
pub static l_Lake_VerRange_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_VerRange_instToString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_VerRange_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerRange_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_VerRange_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_VerRange_instToString___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0_value:
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
    m_data: [60, 101, 109, 112, 116, 121, 62, 0],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0_value
) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 124, 124, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0_value:
    LeanStringObject<58> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 116, 105, 108, 100, 101, 32, 114, 97, 110, 103, 101,
        58, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32,
        111, 102, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 58, 32, 103, 111, 116, 32,
        0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1_value:
    LeanStringObject<15> = LeanStringObject {
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
        44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 49, 45, 51, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0_value:
    LeanStringObject<58> = LeanStringObject {
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
        105, 110, 118, 97, 108, 105, 100, 32, 99, 97, 114, 101, 116, 32, 114, 97, 110, 103, 101,
        58, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32,
        111, 102, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 58, 32, 103, 111, 116, 32,
        0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1_value:
    LeanStringObject<66> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 66,
    m_capacity: 66,
    m_length: 65,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 99, 97, 114, 101, 116, 32, 114, 97, 110, 103, 101,
        58, 32, 96, 94, 48, 46, 48, 46, 48, 96, 32, 105, 115, 32, 100, 101, 103, 101, 110, 101,
        114, 97, 116, 101, 59, 32, 117, 115, 101, 32, 96, 61, 48, 46, 48, 46, 48, 96, 32, 105, 110,
        115, 116, 101, 97, 100, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value:
    LeanStringObject<69> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 69,
    m_capacity: 69,
    m_length: 68,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 112, 97, 116, 99, 104, 32, 118, 101, 114, 115, 105,
        111, 110, 58, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 32, 97, 102, 116, 101,
        114, 32, 97, 32, 119, 105, 108, 100, 99, 97, 114, 100, 32, 109, 117, 115, 116, 32, 98, 101,
        32, 119, 105, 108, 100, 99, 97, 114, 100, 115, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1_value:
    LeanStringObject<183> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 183,
    m_capacity: 183,
    m_length: 180,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32, 114, 97, 110,
        103, 101, 58, 32, 98, 97, 114, 101, 32, 118, 101, 114, 115, 105, 111, 110, 115, 32, 97,
        114, 101, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 59, 32, 105,
        102, 32, 121, 111, 117, 32, 119, 97, 110, 116, 32, 116, 111, 32, 112, 105, 110, 32, 97, 32,
        115, 112, 101, 99, 105, 102, 105, 99, 32, 118, 101, 114, 115, 105, 111, 110, 44, 32, 117,
        115, 101, 32, 39, 61, 39, 32, 98, 101, 102, 111, 114, 101, 32, 116, 104, 101, 32, 102, 117,
        108, 108, 32, 118, 101, 114, 115, 105, 111, 110, 59, 32, 111, 116, 104, 101, 114, 119, 105,
        115, 101, 44, 32, 117, 115, 101, 32, 39, 226, 137, 165, 39, 32, 116, 111, 32, 115, 117,
        112, 112, 111, 114, 116, 32, 105, 116, 32, 97, 110, 100, 32, 102, 117, 116, 117, 114, 101,
        32, 118, 101, 114, 115, 105, 111, 110, 115, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2_value:
    LeanStringObject<69> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 69,
    m_capacity: 69,
    m_length: 68,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 109, 105, 110, 111, 114, 32, 118, 101, 114, 115, 105,
        111, 110, 58, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 32, 97, 102, 116, 101,
        114, 32, 97, 32, 119, 105, 108, 100, 99, 97, 114, 100, 32, 109, 117, 115, 116, 32, 98, 101,
        32, 119, 105, 108, 100, 99, 97, 114, 100, 115, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3_value:
    LeanStringObject<61> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 61,
    m_capacity: 61,
    m_length: 60,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 119, 105, 108, 100, 99, 97, 114, 100, 32, 114, 97,
        110, 103, 101, 58, 32, 105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98,
        101, 114, 32, 111, 102, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 58, 32, 103,
        111, 116, 32, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4_value:
    LeanStringObject<66> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 66,
    m_capacity: 66,
    m_length: 65,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 119, 105, 108, 100, 99, 97, 114, 100, 32, 114, 97,
        110, 103, 101, 58, 32, 119, 105, 108, 100, 99, 97, 114, 100, 32, 118, 101, 114, 115, 105,
        111, 110, 115, 32, 100, 111, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32,
        115, 117, 102, 102, 105, 120, 101, 115, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0_value:
    LeanStringObject<23> = LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32, 114, 97,
        110, 103, 101, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1_value:
    LeanStringObject<29> = LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 39, 124, 39, 32, 97, 102, 116, 101, 114, 32,
        102, 105, 114, 115, 116, 32, 39, 124, 39, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2_value:
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
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3_value:
    LeanStringObject<48> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 116, 105, 108, 100, 101, 32, 114, 97, 110, 103, 101,
        58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32,
        97, 102, 116, 101, 114, 32, 96, 126, 96, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4_value:
    LeanStringObject<48> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 99, 97, 114, 101, 116, 32, 114, 97, 110, 103, 101,
        58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 118, 101, 114, 115, 105, 111, 110, 32,
        97, 102, 116, 101, 114, 32, 96, 94, 96, 0,
    ],
};
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4_value)
        as *mut LeanObject;
pub static l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value:
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
static mut l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(
    mut v_s_3270_: *mut LeanObject,
    mut v_cs_3271_: *mut LeanObject,
    mut v_iniPos_3272_: *mut LeanObject,
    mut v_p_3273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: u8 = 0;
    let mut v_c_3279_: u32 = 0;
    let mut v___y_3281_: u8 = 0;
    let mut v___x_3282_: u32 = 0;
    let mut v___x_3283_: u8 = 0;
    let mut v_c_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3288_: u8 = 0;
    let mut v___x_3289_: u32 = 0;
    let mut v___x_3290_: u8 = 0;
    let mut v___x_3291_: u32 = 0;
    let mut v___x_3292_: u8 = 0;
    let mut v___x_3294_: u32 = 0;
    let mut v___x_3295_: u8 = 0;
    let mut v___x_3296_: u32 = 0;
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3298_: u32 = 0;
    let mut v___x_3299_: u8 = 0;
    let mut v___x_3300_: u32 = 0;
    let mut v___x_3301_: u8 = 0;
    let mut v___x_3302_: u32 = 0;
    let mut v___x_3303_: u8 = 0;
    let mut v_c_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3277_ = lean_string_utf8_byte_size(v_s_3270_);
                v___x_3278_ = lean_nat_dec_eq(v_p_3273_, v___x_3277_);
                if v___x_3278_ == 0 {
                    v_c_3279_ = lean_string_utf8_get_fast(v_s_3270_, v_p_3273_);
                    v___x_3298_ = 46;
                    v___x_3299_ = lean_uint32_dec_eq(v_c_3279_, v___x_3298_);
                    if v___x_3299_ == 0 {
                        v___x_3300_ = 65;
                        v___x_3301_ = lean_uint32_dec_le(v___x_3300_, v_c_3279_);
                        if v___x_3301_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            v___x_3302_ = 90;
                            v___x_3303_ = lean_uint32_dec_le(v_c_3279_, v___x_3302_);
                            if v___x_3303_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_inc(v_p_3273_);
                        lean_inc_ref(v_s_3270_);
                        v_c_3304_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_c_3304_, 0, v_s_3270_);
                        lean_ctor_set(v_c_3304_, 1, v_iniPos_3272_);
                        lean_ctor_set(v_c_3304_, 2, v_p_3273_);
                        v___x_3305_ = lean_array_push(v_cs_3271_, v_c_3304_);
                        v___x_3306_ = lean_string_utf8_next_fast(v_s_3270_, v_p_3273_);
                        lean_dec(v_p_3273_);
                        v_cs_3271_ = v___x_3305_;
                        v_iniPos_3272_ = v___x_3306_;
                        v_p_3273_ = v___x_3306_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_inc(v_p_3273_);
                    v_c_3308_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_c_3308_, 0, v_s_3270_);
                    lean_ctor_set(v_c_3308_, 1, v_iniPos_3272_);
                    lean_ctor_set(v_c_3308_, 2, v_p_3273_);
                    v___x_3309_ = lean_array_push(v_cs_3271_, v_c_3308_);
                    v___x_3310_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3310_, 0, v___x_3309_);
                    lean_ctor_set(v___x_3310_, 1, v_p_3273_);
                    return v___x_3310_;
                }
            }
            1 => {
                v___x_3275_ = lean_string_utf8_next_fast(v_s_3270_, v_p_3273_);
                lean_dec(v_p_3273_);
                v_p_3273_ = v___x_3275_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_3281_ == 0 {
                    v___x_3282_ = 42;
                    v___x_3283_ = lean_uint32_dec_eq(v_c_3279_, v___x_3282_);
                    if v___x_3283_ == 0 {
                        lean_inc(v_p_3273_);
                        v_c_3284_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_c_3284_, 0, v_s_3270_);
                        lean_ctor_set(v_c_3284_, 1, v_iniPos_3272_);
                        lean_ctor_set(v_c_3284_, 2, v_p_3273_);
                        v___x_3285_ = lean_array_push(v_cs_3271_, v_c_3284_);
                        v___x_3286_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3286_, 0, v___x_3285_);
                        lean_ctor_set(v___x_3286_, 1, v_p_3273_);
                        return v___x_3286_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_3288_ == 0 {
                    v___x_3289_ = 48;
                    v___x_3290_ = lean_uint32_dec_le(v___x_3289_, v_c_3279_);
                    if v___x_3290_ == 0 {
                        v___y_3281_ = v___x_3290_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3291_ = 57;
                        v___x_3292_ = lean_uint32_dec_le(v_c_3279_, v___x_3291_);
                        v___y_3281_ = v___x_3292_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_3294_ = 97;
                v___x_3295_ = lean_uint32_dec_le(v___x_3294_, v_c_3279_);
                if v___x_3295_ == 0 {
                    v___y_3288_ = v___x_3295_;
                    state = 3;
                    continue;
                } else {
                    v___x_3296_ = 122;
                    v___x_3297_ = lean_uint32_dec_le(v_c_3279_, v___x_3296_);
                    v___y_3288_ = v___x_3297_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerComponents_go(
    mut v_s_3311_: *mut LeanObject,
    mut v_cs_3312_: *mut LeanObject,
    mut v_iniPos_3313_: *mut LeanObject,
    mut v_p_3314_: *mut LeanObject,
    mut v_iniPos__le_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    v___x_3316_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(
        v_s_3311_,
        v_cs_3312_,
        v_iniPos_3313_,
        v_p_3314_,
    );
    return v___x_3316_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerComponents(
    mut v_s_3319_: *mut LeanObject,
    mut v_p_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    v___x_3321_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0;
    lean_inc(v_p_3320_);
    v___x_3322_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(
        v_s_3319_,
        v___x_3321_,
        v_p_3320_,
        v_p_3320_,
    );
    return v___x_3322_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_isWildVer(
    mut v_s_3323_: *mut LeanObject,
) -> u8 {
    let mut v_str_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: u8 = 0;
    let mut v_c_3333_: u32 = 0;
    let mut v___y_3335_: u8 = 0;
    let mut v___x_3336_: u32 = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: u32 = 0;
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: u32 = 0;
    let mut v___x_3341_: u8 = 0;
    let mut v___x_3342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_3324_ = lean_ctor_get(v_s_3323_, 0);
                v_startInclusive_3325_ = lean_ctor_get(v_s_3323_, 1);
                v_endExclusive_3326_ = lean_ctor_get(v_s_3323_, 2);
                v_p_3327_ = lean_unsigned_to_nat(0);
                v___x_3328_ = lean_nat_sub(v_endExclusive_3326_, v_startInclusive_3325_);
                v___x_3329_ = lean_nat_dec_eq(v_p_3327_, v___x_3328_);
                if v___x_3329_ == 0 {
                    v___x_3330_ = lean_string_utf8_next_fast(v_str_3324_, v_startInclusive_3325_);
                    v___x_3331_ = lean_nat_sub(v___x_3330_, v_startInclusive_3325_);
                    v___x_3332_ = lean_nat_dec_eq(v___x_3331_, v___x_3328_);
                    lean_dec(v___x_3328_);
                    lean_dec(v___x_3331_);
                    if v___x_3332_ == 0 {
                        return v___x_3332_;
                    } else {
                        v_c_3333_ = lean_string_utf8_get_fast(v_str_3324_, v_startInclusive_3325_);
                        v___x_3338_ = 120;
                        v___x_3339_ = lean_uint32_dec_eq(v_c_3333_, v___x_3338_);
                        if v___x_3339_ == 0 {
                            v___x_3340_ = 88;
                            v___x_3341_ = lean_uint32_dec_eq(v_c_3333_, v___x_3340_);
                            v___y_3335_ = v___x_3341_;
                            state = 1;
                            continue;
                        } else {
                            v___y_3335_ = v___x_3339_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3328_);
                    v___x_3342_ = 0;
                    return v___x_3342_;
                }
            }
            1 => {
                if v___y_3335_ == 0 {
                    v___x_3336_ = 42;
                    v___x_3337_ = lean_uint32_dec_eq(v_c_3333_, v___x_3336_);
                    return v___x_3337_;
                } else {
                    return v___y_3335_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_isWildVer___boxed(
    mut v_s_3343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3344_: u8 = 0;
    let mut v_r_3345_: *mut LeanObject = core::ptr::null_mut();
    v_res_3344_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_s_3343_);
    lean_dec_ref(v_s_3343_);
    v_r_3345_ = lean_box((v_res_3344_) as usize);
    return v_r_3345_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(
    mut v_what_3349_: *mut LeanObject,
    mut v_s_3350_: *mut LeanObject,
    mut v_a_3351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    v___x_3352_ = l_String_Slice_toNat_x3f(v_s_3350_);
    if lean_obj_tag(v___x_3352_) == 1 {
        let mut v_val_3353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
        v_val_3353_ = lean_ctor_get(v___x_3352_, 0);
        lean_inc(v_val_3353_);
        lean_dec_ref_known(v___x_3352_, 1);
        v___x_3354_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3354_, 0, v_val_3353_);
        lean_ctor_set(v___x_3354_, 1, v_a_3351_);
        return v___x_3354_;
    } else {
        let mut v_str_3355_: *mut LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_3356_: *mut LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_3357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3352_);
        v_str_3355_ = lean_ctor_get(v_s_3350_, 0);
        v_startInclusive_3356_ = lean_ctor_get(v_s_3350_, 1);
        v_endExclusive_3357_ = lean_ctor_get(v_s_3350_, 2);
        v___x_3358_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0;
        v___x_3359_ = lean_string_append(v___x_3358_, v_what_3349_);
        v___x_3360_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1;
        v___x_3361_ = lean_string_append(v___x_3359_, v___x_3360_);
        v___x_3362_ =
            lean_string_utf8_extract(v_str_3355_, v_startInclusive_3356_, v_endExclusive_3357_);
        v___x_3363_ = lean_string_append(v___x_3361_, v___x_3362_);
        lean_dec_ref(v___x_3362_);
        v___x_3364_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
        v___x_3365_ = lean_string_append(v___x_3363_, v___x_3364_);
        v___x_3366_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3366_, 0, v___x_3365_);
        lean_ctor_set(v___x_3366_, 1, v_a_3351_);
        return v___x_3366_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___boxed(
    mut v_what_3367_: *mut LeanObject,
    mut v_s_3368_: *mut LeanObject,
    mut v_a_3369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3370_: *mut LeanObject = core::ptr::null_mut();
    v_res_3370_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg(
        v_what_3367_,
        v_s_3368_,
        v_a_3369_,
    );
    lean_dec_ref(v_s_3368_);
    lean_dec_ref(v_what_3367_);
    return v_res_3370_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerNat(
    mut v_00_u03c3_3371_: *mut LeanObject,
    mut v_what_3372_: *mut LeanObject,
    mut v_s_3373_: *mut LeanObject,
    mut v_a_3374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    v___x_3375_ = l_String_Slice_toNat_x3f(v_s_3373_);
    if lean_obj_tag(v___x_3375_) == 1 {
        let mut v_val_3376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
        v_val_3376_ = lean_ctor_get(v___x_3375_, 0);
        lean_inc(v_val_3376_);
        lean_dec_ref_known(v___x_3375_, 1);
        v___x_3377_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3377_, 0, v_val_3376_);
        lean_ctor_set(v___x_3377_, 1, v_a_3374_);
        return v___x_3377_;
    } else {
        let mut v_str_3378_: *mut LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_3379_: *mut LeanObject = core::ptr::null_mut();
        let mut v_endExclusive_3380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3375_);
        v_str_3378_ = lean_ctor_get(v_s_3373_, 0);
        v_startInclusive_3379_ = lean_ctor_get(v_s_3373_, 1);
        v_endExclusive_3380_ = lean_ctor_get(v_s_3373_, 2);
        v___x_3381_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0;
        v___x_3382_ = lean_string_append(v___x_3381_, v_what_3372_);
        v___x_3383_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__1;
        v___x_3384_ = lean_string_append(v___x_3382_, v___x_3383_);
        v___x_3385_ =
            lean_string_utf8_extract(v_str_3378_, v_startInclusive_3379_, v_endExclusive_3380_);
        v___x_3386_ = lean_string_append(v___x_3384_, v___x_3385_);
        lean_dec_ref(v___x_3385_);
        v___x_3387_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
        v___x_3388_ = lean_string_append(v___x_3386_, v___x_3387_);
        v___x_3389_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_3389_, 0, v___x_3388_);
        lean_ctor_set(v___x_3389_, 1, v_a_3374_);
        return v___x_3389_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerNat___boxed(
    mut v_00_u03c3_3390_: *mut LeanObject,
    mut v_what_3391_: *mut LeanObject,
    mut v_s_3392_: *mut LeanObject,
    mut v_a_3393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3394_: *mut LeanObject = core::ptr::null_mut();
    v_res_3394_ = l___private_Lake_Util_Version_0__Lake_parseVerNat(
        v_00_u03c3_3390_,
        v_what_3391_,
        v_s_3392_,
        v_a_3393_,
    );
    lean_dec_ref(v_s_3392_);
    lean_dec_ref(v_what_3391_);
    return v_res_3394_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(
    mut v_x_3395_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_3395_) {
        0 => {
            let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
            v___x_3396_ = lean_unsigned_to_nat(0);
            return v___x_3396_;
        }
        1 => {
            let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
            v___x_3397_ = lean_unsigned_to_nat(1);
            return v___x_3397_;
        }
        _ => {
            let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
            v___x_3398_ = lean_unsigned_to_nat(2);
            return v___x_3398_;
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx___boxed(
    mut v_x_3399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3400_: *mut LeanObject = core::ptr::null_mut();
    v_res_3400_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorIdx(v_x_3399_);
    lean_dec(v_x_3399_);
    return v_res_3400_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(
    mut v_t_3401_: *mut LeanObject,
    mut v_k_3402_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_3401_) == 2 {
        let mut v_n_3403_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
        v_n_3403_ = lean_ctor_get(v_t_3401_, 0);
        lean_inc(v_n_3403_);
        lean_dec_ref_known(v_t_3401_, 1);
        v___x_3404_ = lean_apply_1(v_k_3402_, v_n_3403_);
        return v___x_3404_;
    } else {
        lean_dec(v_t_3401_);
        return v_k_3402_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(
    mut v_motive_3405_: *mut LeanObject,
    mut v_ctorIdx_3406_: *mut LeanObject,
    mut v_t_3407_: *mut LeanObject,
    mut v_h_3408_: *mut LeanObject,
    mut v_k_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    v___x_3410_ =
        l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(v_t_3407_, v_k_3409_);
    return v___x_3410_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___boxed(
    mut v_motive_3411_: *mut LeanObject,
    mut v_ctorIdx_3412_: *mut LeanObject,
    mut v_t_3413_: *mut LeanObject,
    mut v_h_3414_: *mut LeanObject,
    mut v_k_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3416_: *mut LeanObject = core::ptr::null_mut();
    v_res_3416_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim(
        v_motive_3411_,
        v_ctorIdx_3412_,
        v_t_3413_,
        v_h_3414_,
        v_k_3415_,
    );
    lean_dec(v_ctorIdx_3412_);
    return v_res_3416_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim___redArg(
    mut v_t_3417_: *mut LeanObject,
    mut v_none_3418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    v___x_3419_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(
        v_t_3417_,
        v_none_3418_,
    );
    return v___x_3419_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_none_elim(
    mut v_motive_3420_: *mut LeanObject,
    mut v_t_3421_: *mut LeanObject,
    mut v_h_3422_: *mut LeanObject,
    mut v_none_3423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(
        v_t_3421_,
        v_none_3423_,
    );
    return v___x_3424_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim___redArg(
    mut v_t_3425_: *mut LeanObject,
    mut v_wild_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v___x_3427_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(
        v_t_3425_,
        v_wild_3426_,
    );
    return v___x_3427_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_wild_elim(
    mut v_motive_3428_: *mut LeanObject,
    mut v_t_3429_: *mut LeanObject,
    mut v_h_3430_: *mut LeanObject,
    mut v_wild_3431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    v___x_3432_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(
        v_t_3429_,
        v_wild_3431_,
    );
    return v___x_3432_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim___redArg(
    mut v_t_3433_: *mut LeanObject,
    mut v_nat_3434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    v___x_3435_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(
        v_t_3433_,
        v_nat_3434_,
    );
    return v___x_3435_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComponent_nat_elim(
    mut v_motive_3436_: *mut LeanObject,
    mut v_t_3437_: *mut LeanObject,
    mut v_h_3438_: *mut LeanObject,
    mut v_nat_3439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3440_ = l___private_Lake_Util_Version_0__Lake_VerComponent_ctorElim___redArg(
        v_t_3437_,
        v_nat_3439_,
    );
    return v___x_3440_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(
    mut v_what_3442_: *mut LeanObject,
    mut v_s_x3f_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: u8 = 0;
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3451_: u8 = 0;
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3456_: u8 = 0;
    let mut v_str_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_x3f_3443_) == 1 {
                    v_val_3445_ = lean_ctor_get(v_s_x3f_3443_, 0);
                    v___x_3446_ = l___private_Lake_Util_Version_0__Lake_isWildVer(v_val_3445_);
                    if v___x_3446_ == 0 {
                        v___x_3447_ = l_String_Slice_toNat_x3f(v_val_3445_);
                        if lean_obj_tag(v___x_3447_) == 1 {
                            v_val_3448_ = lean_ctor_get(v___x_3447_, 0);
                            v_isSharedCheck_3456_ = (!lean_is_exclusive(v___x_3447_)) as u8;
                            if v_isSharedCheck_3456_ == 0 {
                                v___x_3450_ = v___x_3447_;
                                v_isShared_3451_ = v_isSharedCheck_3456_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_val_3448_);
                                lean_dec(v___x_3447_);
                                v___x_3450_ = lean_box(0);
                                v_isShared_3451_ = v_isSharedCheck_3456_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_3447_);
                            v_str_3457_ = lean_ctor_get(v_val_3445_, 0);
                            v_startInclusive_3458_ = lean_ctor_get(v_val_3445_, 1);
                            v_endExclusive_3459_ = lean_ctor_get(v_val_3445_, 2);
                            v___x_3460_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__0;
                            v___x_3461_ = lean_string_append(v___x_3460_, v_what_3442_);
                            v___x_3462_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___closed__0;
                            v___x_3463_ = lean_string_append(v___x_3461_, v___x_3462_);
                            v___x_3464_ = lean_string_utf8_extract(
                                v_str_3457_,
                                v_startInclusive_3458_,
                                v_endExclusive_3459_,
                            );
                            v___x_3465_ = lean_string_append(v___x_3463_, v___x_3464_);
                            lean_dec_ref(v___x_3464_);
                            v___x_3466_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                            v___x_3467_ = lean_string_append(v___x_3465_, v___x_3466_);
                            v___x_3468_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_3468_, 0, v___x_3467_);
                            lean_ctor_set(v___x_3468_, 1, v_a_3444_);
                            return v___x_3468_;
                        }
                    } else {
                        v___x_3469_ = lean_box(1);
                        v___x_3470_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3470_, 0, v___x_3469_);
                        lean_ctor_set(v___x_3470_, 1, v_a_3444_);
                        return v___x_3470_;
                    }
                } else {
                    v___x_3471_ = lean_box(0);
                    v___x_3472_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3472_, 0, v___x_3471_);
                    lean_ctor_set(v___x_3472_, 1, v_a_3444_);
                    return v___x_3472_;
                }
            }
            1 => {
                if v_isShared_3451_ == 0 {
                    lean_ctor_set_tag(v___x_3450_, 2);
                    v___x_3453_ = v___x_3450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3455_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_val_3448_);
                    v___x_3453_ = v_reuseFailAlloc_3455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3454_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3454_, 0, v___x_3453_);
                lean_ctor_set(v___x_3454_, 1, v_a_3444_);
                return v___x_3454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg___boxed(
    mut v_what_3473_: *mut LeanObject,
    mut v_s_x3f_3474_: *mut LeanObject,
    mut v_a_3475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3476_: *mut LeanObject = core::ptr::null_mut();
    v_res_3476_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(
        v_what_3473_,
        v_s_x3f_3474_,
        v_a_3475_,
    );
    lean_dec(v_s_x3f_3474_);
    lean_dec_ref(v_what_3473_);
    return v_res_3476_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerComponent(
    mut v_00_u03c3_3477_: *mut LeanObject,
    mut v_what_3478_: *mut LeanObject,
    mut v_s_x3f_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(
        v_what_3478_,
        v_s_x3f_3479_,
        v_a_3480_,
    );
    return v___x_3481_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseVerComponent___boxed(
    mut v_00_u03c3_3482_: *mut LeanObject,
    mut v_what_3483_: *mut LeanObject,
    mut v_s_x3f_3484_: *mut LeanObject,
    mut v_a_3485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3486_: *mut LeanObject = core::ptr::null_mut();
    v_res_3486_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent(
        v_00_u03c3_3482_,
        v_what_3483_,
        v_s_x3f_3484_,
        v_a_3485_,
    );
    lean_dec(v_s_x3f_3484_);
    lean_dec_ref(v_what_3483_);
    return v_res_3486_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(
    mut v_s_3487_: *mut LeanObject,
    mut v_p_3488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: u8 = 0;
    let mut v___x_3495_: u32 = 0;
    let mut v___y_3497_: u8 = 0;
    let mut v___x_3498_: u32 = 0;
    let mut v___x_3499_: u8 = 0;
    let mut v___x_3500_: u32 = 0;
    let mut v___x_3501_: u8 = 0;
    let mut v___x_3502_: u32 = 0;
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: u32 = 0;
    let mut v___x_3505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3493_ = lean_string_utf8_byte_size(v_s_3487_);
                v___x_3494_ = lean_nat_dec_eq(v_p_3488_, v___x_3493_);
                if v___x_3494_ == 0 {
                    v___x_3495_ = lean_string_utf8_get_fast(v_s_3487_, v_p_3488_);
                    v___x_3502_ = 32;
                    v___x_3503_ = lean_uint32_dec_eq(v___x_3495_, v___x_3502_);
                    if v___x_3503_ == 0 {
                        v___x_3504_ = 9;
                        v___x_3505_ = lean_uint32_dec_eq(v___x_3495_, v___x_3504_);
                        v___y_3497_ = v___x_3505_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3497_ = v___x_3503_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_p_3488_;
                }
            }
            1 => {
                if v___y_3490_ == 0 {
                    v___x_3491_ = lean_string_utf8_next_fast(v_s_3487_, v_p_3488_);
                    lean_dec(v_p_3488_);
                    v_p_3488_ = v___x_3491_;
                    state = 0;
                    continue;
                } else {
                    return v_p_3488_;
                }
            }
            2 => {
                if v___y_3497_ == 0 {
                    v___x_3498_ = 13;
                    v___x_3499_ = lean_uint32_dec_eq(v___x_3495_, v___x_3498_);
                    if v___x_3499_ == 0 {
                        v___x_3500_ = 10;
                        v___x_3501_ = lean_uint32_dec_eq(v___x_3495_, v___x_3500_);
                        v___y_3490_ = v___x_3501_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3490_ = v___x_3499_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_p_3488_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace___boxed(
    mut v_s_3506_: *mut LeanObject,
    mut v_p_3507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3508_: *mut LeanObject = core::ptr::null_mut();
    v_res_3508_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(
        v_s_3506_, v_p_3507_,
    );
    lean_dec_ref(v_s_3506_);
    return v_res_3508_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(
    mut v_s_3509_: *mut LeanObject,
    mut v_a_3510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: u8 = 0;
    v___x_3511_ = lean_string_utf8_byte_size(v_s_3509_);
    v___x_3512_ = lean_nat_dec_eq(v_a_3510_, v___x_3511_);
    if v___x_3512_ == 0 {
        let mut v___x_3513_: u32 = 0;
        let mut v___x_3514_: u32 = 0;
        let mut v___x_3515_: u8 = 0;
        v___x_3513_ = lean_string_utf8_get_fast(v_s_3509_, v_a_3510_);
        v___x_3514_ = 45;
        v___x_3515_ = lean_uint32_dec_eq(v___x_3513_, v___x_3514_);
        if v___x_3515_ == 0 {
            let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
            v___x_3516_ = lean_box(0);
            v___x_3517_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3517_, 0, v___x_3516_);
            lean_ctor_set(v___x_3517_, 1, v_a_3510_);
            return v___x_3517_;
        } else {
            let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
            v___x_3518_ = lean_string_utf8_next_fast(v_s_3509_, v_a_3510_);
            lean_dec(v_a_3510_);
            v___x_3519_ =
                l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f_nextUntilWhitespace(
                    v_s_3509_,
                    v___x_3518_,
                );
            v___x_3520_ = lean_string_utf8_extract(v_s_3509_, v___x_3518_, v___x_3519_);
            v___x_3521_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3521_, 0, v___x_3520_);
            v___x_3522_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3522_, 0, v___x_3521_);
            lean_ctor_set(v___x_3522_, 1, v___x_3519_);
            return v___x_3522_;
        }
    } else {
        let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
        v___x_3523_ = lean_box(0);
        v___x_3524_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3524_, 0, v___x_3523_);
        lean_ctor_set(v___x_3524_, 1, v_a_3510_);
        return v___x_3524_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f___boxed(
    mut v_s_3525_: *mut LeanObject,
    mut v_a_3526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3527_: *mut LeanObject = core::ptr::null_mut();
    v_res_3527_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(v_s_3525_, v_a_3526_);
    lean_dec_ref(v_s_3525_);
    return v_res_3527_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(
    mut v_s_3530_: *mut LeanObject,
    mut v_a_3531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v_val_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3549_: u8 = 0;
    let mut v_unused_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3559_: u8 = 0;
    let mut v_unused_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3532_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(
                    v_s_3530_, v_a_3531_,
                );
                v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
                lean_inc(v_a_3533_);
                if lean_obj_tag(v_a_3533_) == 1 {
                    v_a_3534_ = lean_ctor_get(v___x_3532_, 1);
                    v_isSharedCheck_3549_ = (!lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3549_ == 0 {
                        v_unused_3550_ = lean_ctor_get(v___x_3532_, 0);
                        lean_dec(v_unused_3550_);
                        v___x_3536_ = v___x_3532_;
                        v_isShared_3537_ = v_isSharedCheck_3549_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3534_);
                        lean_dec(v___x_3532_);
                        v___x_3536_ = lean_box(0);
                        v_isShared_3537_ = v_isSharedCheck_3549_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3533_);
                    v_a_3551_ = lean_ctor_get(v___x_3532_, 1);
                    v_isSharedCheck_3559_ = (!lean_is_exclusive(v___x_3532_)) as u8;
                    if v_isSharedCheck_3559_ == 0 {
                        v_unused_3560_ = lean_ctor_get(v___x_3532_, 0);
                        lean_dec(v_unused_3560_);
                        v___x_3553_ = v___x_3532_;
                        v_isShared_3554_ = v_isSharedCheck_3559_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_3551_);
                        lean_dec(v___x_3532_);
                        v___x_3553_ = lean_box(0);
                        v_isShared_3554_ = v_isSharedCheck_3559_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_val_3538_ = lean_ctor_get(v_a_3533_, 0);
                lean_inc(v_val_3538_);
                lean_dec_ref_known(v_a_3533_, 1);
                v___x_3539_ = lean_string_utf8_byte_size(v_val_3538_);
                v___x_3540_ = lean_unsigned_to_nat(0);
                v___x_3541_ = lean_nat_dec_eq(v___x_3539_, v___x_3540_);
                if v___x_3541_ == 0 {
                    if v_isShared_3537_ == 0 {
                        lean_ctor_set(v___x_3536_, 0, v_val_3538_);
                        v___x_3543_ = v___x_3536_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_val_3538_);
                        lean_ctor_set(v_reuseFailAlloc_3544_, 1, v_a_3534_);
                        v___x_3543_ = v_reuseFailAlloc_3544_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_val_3538_);
                    v___x_3545_ =
                        l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__0;
                    if v_isShared_3537_ == 0 {
                        lean_ctor_set_tag(v___x_3536_, 1);
                        lean_ctor_set(v___x_3536_, 0, v___x_3545_);
                        v___x_3547_ = v___x_3536_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3545_);
                        lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_a_3534_);
                        v___x_3547_ = v_reuseFailAlloc_3548_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3543_;
            }
            3 => {
                return v___x_3547_;
            }
            4 => {
                v___x_3555_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                if v_isShared_3554_ == 0 {
                    lean_ctor_set(v___x_3553_, 0, v___x_3555_);
                    v___x_3557_ = v___x_3553_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
                    lean_ctor_set(v_reuseFailAlloc_3558_, 1, v_a_3551_);
                    v___x_3557_ = v_reuseFailAlloc_3558_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3557_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___boxed(
    mut v_s_3561_: *mut LeanObject,
    mut v_a_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3563_: *mut LeanObject = core::ptr::null_mut();
    v_res_3563_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_3561_, v_a_3562_);
    lean_dec_ref(v_s_3561_);
    return v_res_3563_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(
    mut v_s_3565_: *mut LeanObject,
    mut v_x_3566_: *mut LeanObject,
    mut v_startPos_3567_: *mut LeanObject,
    mut v_endPos_3568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_3565_);
    v___x_3569_ = lean_apply_2(v_x_3566_, v_s_3565_, v_startPos_3567_);
    if lean_obj_tag(v___x_3569_) == 0 {
        let mut v_a_3570_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_3571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3572_: u8 = 0;
        v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
        lean_inc(v_a_3570_);
        v_a_3571_ = lean_ctor_get(v___x_3569_, 1);
        lean_inc(v_a_3571_);
        lean_dec_ref_known(v___x_3569_, 2);
        v___x_3572_ = lean_nat_dec_eq(v_a_3571_, v_endPos_3568_);
        if v___x_3572_ == 0 {
            let mut v_tail_3573_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_3570_);
            v_tail_3573_ = lean_string_utf8_extract(v_s_3565_, v_a_3571_, v_endPos_3568_);
            lean_dec(v_a_3571_);
            lean_dec_ref(v_s_3565_);
            v___x_3574_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0;
            v___x_3575_ = lean_string_append(v___x_3574_, v_tail_3573_);
            lean_dec_ref(v_tail_3573_);
            v___x_3576_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_3576_, 0, v___x_3575_);
            return v___x_3576_;
        } else {
            let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_3571_);
            lean_dec_ref(v_s_3565_);
            v___x_3577_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3577_, 0, v_a_3570_);
            return v___x_3577_;
        }
    } else {
        let mut v_a_3578_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_3565_);
        v_a_3578_ = lean_ctor_get(v___x_3569_, 0);
        lean_inc(v_a_3578_);
        lean_dec_ref_known(v___x_3569_, 2);
        v___x_3579_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3579_, 0, v_a_3578_);
        return v___x_3579_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___boxed(
    mut v_s_3580_: *mut LeanObject,
    mut v_x_3581_: *mut LeanObject,
    mut v_startPos_3582_: *mut LeanObject,
    mut v_endPos_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3584_: *mut LeanObject = core::ptr::null_mut();
    v_res_3584_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg(
        v_s_3580_,
        v_x_3581_,
        v_startPos_3582_,
        v_endPos_3583_,
    );
    lean_dec(v_endPos_3583_);
    return v_res_3584_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_runVerParse(
    mut v_00_u03b1_3585_: *mut LeanObject,
    mut v_s_3586_: *mut LeanObject,
    mut v_x_3587_: *mut LeanObject,
    mut v_startPos_3588_: *mut LeanObject,
    mut v_endPos_3589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_3586_);
    v___x_3590_ = lean_apply_2(v_x_3587_, v_s_3586_, v_startPos_3588_);
    if lean_obj_tag(v___x_3590_) == 0 {
        let mut v_a_3591_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_3592_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3593_: u8 = 0;
        v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
        lean_inc(v_a_3591_);
        v_a_3592_ = lean_ctor_get(v___x_3590_, 1);
        lean_inc(v_a_3592_);
        lean_dec_ref_known(v___x_3590_, 2);
        v___x_3593_ = lean_nat_dec_eq(v_a_3592_, v_endPos_3589_);
        if v___x_3593_ == 0 {
            let mut v_tail_3594_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_3591_);
            v_tail_3594_ = lean_string_utf8_extract(v_s_3586_, v_a_3592_, v_endPos_3589_);
            lean_dec(v_a_3592_);
            lean_dec_ref(v_s_3586_);
            v___x_3595_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0;
            v___x_3596_ = lean_string_append(v___x_3595_, v_tail_3594_);
            lean_dec_ref(v_tail_3594_);
            v___x_3597_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_3597_, 0, v___x_3596_);
            return v___x_3597_;
        } else {
            let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_3592_);
            lean_dec_ref(v_s_3586_);
            v___x_3598_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3598_, 0, v_a_3591_);
            return v___x_3598_;
        }
    } else {
        let mut v_a_3599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_3586_);
        v_a_3599_ = lean_ctor_get(v___x_3590_, 0);
        lean_inc(v_a_3599_);
        lean_dec_ref_known(v___x_3590_, 2);
        v___x_3600_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3600_, 0, v_a_3599_);
        return v___x_3600_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_runVerParse___boxed(
    mut v_00_u03b1_3601_: *mut LeanObject,
    mut v_s_3602_: *mut LeanObject,
    mut v_x_3603_: *mut LeanObject,
    mut v_startPos_3604_: *mut LeanObject,
    mut v_endPos_3605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3606_: *mut LeanObject = core::ptr::null_mut();
    v_res_3606_ = l___private_Lake_Util_Version_0__Lake_runVerParse(
        v_00_u03b1_3601_,
        v_s_3602_,
        v_x_3603_,
        v_startPos_3604_,
        v_endPos_3605_,
    );
    lean_dec(v_endPos_3605_);
    return v_res_3606_;
}
pub unsafe fn l_Nat_cast___at___00Lake_instReprSemVerCore_repr_spec__0(
    mut v_a_3611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    v___x_3612_ = lean_nat_to_int(v_a_3611_);
    return v___x_3612_;
}
pub unsafe fn _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    v___x_3626_ = lean_unsigned_to_nat(9);
    v___x_3627_ = lean_nat_to_int(v___x_3626_);
    return v___x_3627_;
}
pub unsafe fn _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15() -> *mut LeanObject {
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    v___x_3638_ = l_Lake_instReprSemVerCore_repr___redArg___closed__0;
    v___x_3639_ = lean_string_length(v___x_3638_);
    return v___x_3639_;
}
pub unsafe fn _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16() -> *mut LeanObject {
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    v___x_3640_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__15),
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__15_once),
        _init_l_Lake_instReprSemVerCore_repr___redArg___closed__15,
    );
    v___x_3641_ = lean_nat_to_int(v___x_3640_);
    return v___x_3641_;
}
pub unsafe fn l_Lake_instReprSemVerCore_repr___redArg(
    mut v_x_3646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_major_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minor_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patch_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: u8 = 0;
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v_major_3647_ = lean_ctor_get(v_x_3646_, 0);
    lean_inc(v_major_3647_);
    v_minor_3648_ = lean_ctor_get(v_x_3646_, 1);
    lean_inc(v_minor_3648_);
    v_patch_3649_ = lean_ctor_get(v_x_3646_, 2);
    lean_inc(v_patch_3649_);
    lean_dec_ref(v_x_3646_);
    v___x_3650_ = l_Lake_instReprSemVerCore_repr___redArg___closed__5;
    v___x_3651_ = l_Lake_instReprSemVerCore_repr___redArg___closed__6;
    v___x_3652_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__7_once),
        _init_l_Lake_instReprSemVerCore_repr___redArg___closed__7,
    );
    v___x_3653_ = l_Nat_reprFast(v_major_3647_);
    v___x_3654_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3654_, 0, v___x_3653_);
    v___x_3655_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3655_, 0, v___x_3652_);
    lean_ctor_set(v___x_3655_, 1, v___x_3654_);
    v___x_3656_ = 0;
    v___x_3657_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3657_, 0, v___x_3655_);
    lean_ctor_set_uint8(
        v___x_3657_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3656_,
    );
    v___x_3658_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3658_, 0, v___x_3651_);
    lean_ctor_set(v___x_3658_, 1, v___x_3657_);
    v___x_3659_ = l_Lake_instReprSemVerCore_repr___redArg___closed__9;
    v___x_3660_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3660_, 0, v___x_3658_);
    lean_ctor_set(v___x_3660_, 1, v___x_3659_);
    v___x_3661_ = lean_box(1);
    v___x_3662_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3662_, 0, v___x_3660_);
    lean_ctor_set(v___x_3662_, 1, v___x_3661_);
    v___x_3663_ = l_Lake_instReprSemVerCore_repr___redArg___closed__11;
    v___x_3664_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3664_, 0, v___x_3662_);
    lean_ctor_set(v___x_3664_, 1, v___x_3663_);
    v___x_3665_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3665_, 0, v___x_3664_);
    lean_ctor_set(v___x_3665_, 1, v___x_3650_);
    v___x_3666_ = l_Nat_reprFast(v_minor_3648_);
    v___x_3667_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    v___x_3668_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3668_, 0, v___x_3652_);
    lean_ctor_set(v___x_3668_, 1, v___x_3667_);
    v___x_3669_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3669_, 0, v___x_3668_);
    lean_ctor_set_uint8(
        v___x_3669_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3656_,
    );
    v___x_3670_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3670_, 0, v___x_3665_);
    lean_ctor_set(v___x_3670_, 1, v___x_3669_);
    v___x_3671_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3671_, 0, v___x_3670_);
    lean_ctor_set(v___x_3671_, 1, v___x_3659_);
    v___x_3672_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3672_, 0, v___x_3671_);
    lean_ctor_set(v___x_3672_, 1, v___x_3661_);
    v___x_3673_ = l_Lake_instReprSemVerCore_repr___redArg___closed__13;
    v___x_3674_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3674_, 0, v___x_3672_);
    lean_ctor_set(v___x_3674_, 1, v___x_3673_);
    v___x_3675_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3675_, 0, v___x_3674_);
    lean_ctor_set(v___x_3675_, 1, v___x_3650_);
    v___x_3676_ = l_Nat_reprFast(v_patch_3649_);
    v___x_3677_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3677_, 0, v___x_3676_);
    v___x_3678_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3678_, 0, v___x_3652_);
    lean_ctor_set(v___x_3678_, 1, v___x_3677_);
    v___x_3679_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3679_, 0, v___x_3678_);
    lean_ctor_set_uint8(
        v___x_3679_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3656_,
    );
    v___x_3680_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3680_, 0, v___x_3675_);
    lean_ctor_set(v___x_3680_, 1, v___x_3679_);
    v___x_3681_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__16_once),
        _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16,
    );
    v___x_3682_ = l_Lake_instReprSemVerCore_repr___redArg___closed__17;
    v___x_3683_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3683_, 0, v___x_3682_);
    lean_ctor_set(v___x_3683_, 1, v___x_3680_);
    v___x_3684_ = l_Lake_instReprSemVerCore_repr___redArg___closed__18;
    v___x_3685_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_3685_, 0, v___x_3683_);
    lean_ctor_set(v___x_3685_, 1, v___x_3684_);
    v___x_3686_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_3686_, 0, v___x_3681_);
    lean_ctor_set(v___x_3686_, 1, v___x_3685_);
    v___x_3687_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_3687_, 0, v___x_3686_);
    lean_ctor_set_uint8(
        v___x_3687_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_3656_,
    );
    return v___x_3687_;
}
pub unsafe fn l_Lake_instReprSemVerCore_repr(
    mut v_x_3688_: *mut LeanObject,
    mut v_prec_3689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    v___x_3690_ = l_Lake_instReprSemVerCore_repr___redArg(v_x_3688_);
    return v___x_3690_;
}
pub unsafe fn l_Lake_instReprSemVerCore_repr___boxed(
    mut v_x_3691_: *mut LeanObject,
    mut v_prec_3692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3693_: *mut LeanObject = core::ptr::null_mut();
    v_res_3693_ = l_Lake_instReprSemVerCore_repr(v_x_3691_, v_prec_3692_);
    lean_dec(v_prec_3692_);
    return v_res_3693_;
}
pub unsafe fn l_Lake_instDecidableEqSemVerCore_decEq(
    mut v_x_3696_: *mut LeanObject,
    mut v_x_3697_: *mut LeanObject,
) -> u8 {
    let mut v_major_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minor_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patch_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_major_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minor_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patch_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: u8 = 0;
    v_major_3698_ = lean_ctor_get(v_x_3696_, 0);
    v_minor_3699_ = lean_ctor_get(v_x_3696_, 1);
    v_patch_3700_ = lean_ctor_get(v_x_3696_, 2);
    v_major_3701_ = lean_ctor_get(v_x_3697_, 0);
    v_minor_3702_ = lean_ctor_get(v_x_3697_, 1);
    v_patch_3703_ = lean_ctor_get(v_x_3697_, 2);
    v___x_3704_ = lean_nat_dec_eq(v_major_3698_, v_major_3701_);
    if v___x_3704_ == 0 {
        return v___x_3704_;
    } else {
        let mut v___x_3705_: u8 = 0;
        v___x_3705_ = lean_nat_dec_eq(v_minor_3699_, v_minor_3702_);
        if v___x_3705_ == 0 {
            return v___x_3705_;
        } else {
            let mut v___x_3706_: u8 = 0;
            v___x_3706_ = lean_nat_dec_eq(v_patch_3700_, v_patch_3703_);
            return v___x_3706_;
        }
    }
}
pub unsafe fn l_Lake_instDecidableEqSemVerCore_decEq___boxed(
    mut v_x_3707_: *mut LeanObject,
    mut v_x_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3709_: u8 = 0;
    let mut v_r_3710_: *mut LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_3707_, v_x_3708_);
    lean_dec_ref(v_x_3708_);
    lean_dec_ref(v_x_3707_);
    v_r_3710_ = lean_box((v_res_3709_) as usize);
    return v_r_3710_;
}
pub unsafe fn l_Lake_instDecidableEqSemVerCore(
    mut v_x_3711_: *mut LeanObject,
    mut v_x_3712_: *mut LeanObject,
) -> u8 {
    let mut v___x_3713_: u8 = 0;
    v___x_3713_ = l_Lake_instDecidableEqSemVerCore_decEq(v_x_3711_, v_x_3712_);
    return v___x_3713_;
}
pub unsafe fn l_Lake_instDecidableEqSemVerCore___boxed(
    mut v_x_3714_: *mut LeanObject,
    mut v_x_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3716_: u8 = 0;
    let mut v_r_3717_: *mut LeanObject = core::ptr::null_mut();
    v_res_3716_ = l_Lake_instDecidableEqSemVerCore(v_x_3714_, v_x_3715_);
    lean_dec_ref(v_x_3715_);
    lean_dec_ref(v_x_3714_);
    v_r_3717_ = lean_box((v_res_3716_) as usize);
    return v_r_3717_;
}
pub unsafe fn l_Lake_instOrdSemVerCore_ord(
    mut v_x_3718_: *mut LeanObject,
    mut v_x_3719_: *mut LeanObject,
) -> u8 {
    let mut v_major_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minor_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patch_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_major_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minor_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patch_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    v_major_3720_ = lean_ctor_get(v_x_3718_, 0);
    v_minor_3721_ = lean_ctor_get(v_x_3718_, 1);
    v_patch_3722_ = lean_ctor_get(v_x_3718_, 2);
    v_major_3723_ = lean_ctor_get(v_x_3719_, 0);
    v_minor_3724_ = lean_ctor_get(v_x_3719_, 1);
    v_patch_3725_ = lean_ctor_get(v_x_3719_, 2);
    v___x_3726_ = lean_nat_dec_lt(v_major_3720_, v_major_3723_);
    if v___x_3726_ == 0 {
        let mut v___x_3727_: u8 = 0;
        v___x_3727_ = lean_nat_dec_eq(v_major_3720_, v_major_3723_);
        if v___x_3727_ == 0 {
            let mut v___x_3728_: u8 = 0;
            v___x_3728_ = 2;
            return v___x_3728_;
        } else {
            let mut v___x_3729_: u8 = 0;
            v___x_3729_ = lean_nat_dec_lt(v_minor_3721_, v_minor_3724_);
            if v___x_3729_ == 0 {
                let mut v___x_3730_: u8 = 0;
                v___x_3730_ = lean_nat_dec_eq(v_minor_3721_, v_minor_3724_);
                if v___x_3730_ == 0 {
                    let mut v___x_3731_: u8 = 0;
                    v___x_3731_ = 2;
                    return v___x_3731_;
                } else {
                    let mut v___x_3732_: u8 = 0;
                    v___x_3732_ = lean_nat_dec_lt(v_patch_3722_, v_patch_3725_);
                    if v___x_3732_ == 0 {
                        let mut v___x_3733_: u8 = 0;
                        v___x_3733_ = lean_nat_dec_eq(v_patch_3722_, v_patch_3725_);
                        if v___x_3733_ == 0 {
                            let mut v___x_3734_: u8 = 0;
                            v___x_3734_ = 2;
                            return v___x_3734_;
                        } else {
                            let mut v___x_3735_: u8 = 0;
                            v___x_3735_ = 1;
                            return v___x_3735_;
                        }
                    } else {
                        let mut v___x_3736_: u8 = 0;
                        v___x_3736_ = 0;
                        return v___x_3736_;
                    }
                }
            } else {
                let mut v___x_3737_: u8 = 0;
                v___x_3737_ = 0;
                return v___x_3737_;
            }
        }
    } else {
        let mut v___x_3738_: u8 = 0;
        v___x_3738_ = 0;
        return v___x_3738_;
    }
}
pub unsafe fn l_Lake_instOrdSemVerCore_ord___boxed(
    mut v_x_3739_: *mut LeanObject,
    mut v_x_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3741_: u8 = 0;
    let mut v_r_3742_: *mut LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_Lake_instOrdSemVerCore_ord(v_x_3739_, v_x_3740_);
    lean_dec_ref(v_x_3740_);
    lean_dec_ref(v_x_3739_);
    v_r_3742_ = lean_box((v_res_3741_) as usize);
    return v_r_3742_;
}
pub unsafe fn _init_l_Lake_SemVerCore_instLT() -> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = lean_box(0);
    return v___x_3745_;
}
pub unsafe fn _init_l_Lake_SemVerCore_instLE() -> *mut LeanObject {
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3746_ = lean_box(0);
    return v___x_3746_;
}
pub unsafe fn l_Lake_SemVerCore_instMin___lam__0(
    mut v_x_3747_: *mut LeanObject,
    mut v_y_3748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3749_: u8 = 0;
    v___x_3749_ = l_Lake_instOrdSemVerCore_ord(v_x_3747_, v_y_3748_);
    if v___x_3749_ == 2 {
        lean_inc_ref(v_y_3748_);
        return v_y_3748_;
    } else {
        lean_inc_ref(v_x_3747_);
        return v_x_3747_;
    }
}
pub unsafe fn l_Lake_SemVerCore_instMin___lam__0___boxed(
    mut v_x_3750_: *mut LeanObject,
    mut v_y_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3752_: *mut LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Lake_SemVerCore_instMin___lam__0(v_x_3750_, v_y_3751_);
    lean_dec_ref(v_y_3751_);
    lean_dec_ref(v_x_3750_);
    return v_res_3752_;
}
pub unsafe fn l_Lake_SemVerCore_instMax___lam__0(
    mut v_x_3755_: *mut LeanObject,
    mut v_y_3756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3757_: u8 = 0;
    v___x_3757_ = l_Lake_instOrdSemVerCore_ord(v_x_3755_, v_y_3756_);
    if v___x_3757_ == 2 {
        lean_inc_ref(v_x_3755_);
        return v_x_3755_;
    } else {
        lean_inc_ref(v_y_3756_);
        return v_y_3756_;
    }
}
pub unsafe fn l_Lake_SemVerCore_instMax___lam__0___boxed(
    mut v_x_3758_: *mut LeanObject,
    mut v_y_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3760_: *mut LeanObject = core::ptr::null_mut();
    v_res_3760_ = l_Lake_SemVerCore_instMax___lam__0(v_x_3758_, v_y_3759_);
    lean_dec_ref(v_y_3759_);
    lean_dec_ref(v_x_3758_);
    return v_res_3760_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(
    mut v_s_3769_: *mut LeanObject,
    mut v_a_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3784_: u8 = 0;
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: u8 = 0;
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3832_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3777_ = lean_unsigned_to_nat(0);
                v___x_3778_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0;
                lean_inc(v_a_3770_);
                v___x_3779_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(
                    v_s_3769_,
                    v___x_3778_,
                    v_a_3770_,
                    v_a_3770_,
                );
                v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
                v_a_3781_ = lean_ctor_get(v___x_3779_, 1);
                v_isSharedCheck_3832_ = (!lean_is_exclusive(v___x_3779_)) as u8;
                if v_isSharedCheck_3832_ == 0 {
                    v___x_3783_ = v___x_3779_;
                    v_isShared_3784_ = v_isSharedCheck_3832_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_3781_);
                    lean_inc(v_a_3780_);
                    lean_dec(v___x_3779_);
                    v___x_3783_ = lean_box(0);
                    v_isShared_3784_ = v_isSharedCheck_3832_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_3774_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__0;
                v___x_3775_ = lean_string_append(v___x_3774_, v_a_3772_);
                lean_dec_ref(v_a_3772_);
                v___x_3776_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3776_, 0, v___x_3775_);
                lean_ctor_set(v___x_3776_, 1, v_a_3773_);
                return v___x_3776_;
            }
            2 => {
                v___x_3785_ = lean_array_get_size(v_a_3780_);
                v___x_3786_ = lean_unsigned_to_nat(3);
                v___x_3787_ = lean_nat_dec_eq(v___x_3785_, v___x_3786_);
                if v___x_3787_ == 0 {
                    lean_del_object(v___x_3783_);
                    lean_dec(v_a_3780_);
                    v___x_3788_ =
                        l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__1;
                    v___x_3789_ = l_Nat_reprFast(v___x_3785_);
                    v___x_3790_ = lean_string_append(v___x_3788_, v___x_3789_);
                    lean_dec_ref(v___x_3789_);
                    v___x_3791_ =
                        l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__2;
                    v___x_3792_ = lean_string_append(v___x_3790_, v___x_3791_);
                    v_a_3772_ = v___x_3792_;
                    v_a_3773_ = v_a_3781_;
                    state = 1;
                    continue;
                } else {
                    v___x_3793_ = lean_array_fget_borrowed(v_a_3780_, v___x_3777_);
                    v___x_3794_ = l_String_Slice_toNat_x3f(v___x_3793_);
                    if lean_obj_tag(v___x_3794_) == 1 {
                        v_val_3795_ = lean_ctor_get(v___x_3794_, 0);
                        lean_inc(v_val_3795_);
                        lean_dec_ref_known(v___x_3794_, 1);
                        v___x_3796_ = lean_unsigned_to_nat(1);
                        v___x_3797_ = lean_array_fget_borrowed(v_a_3780_, v___x_3796_);
                        v___x_3798_ = l_String_Slice_toNat_x3f(v___x_3797_);
                        if lean_obj_tag(v___x_3798_) == 1 {
                            v_val_3799_ = lean_ctor_get(v___x_3798_, 0);
                            lean_inc(v_val_3799_);
                            lean_dec_ref_known(v___x_3798_, 1);
                            v___x_3800_ = lean_unsigned_to_nat(2);
                            v___x_3801_ = lean_array_fget(v_a_3780_, v___x_3800_);
                            lean_dec(v_a_3780_);
                            v___x_3802_ = l_String_Slice_toNat_x3f(v___x_3801_);
                            if lean_obj_tag(v___x_3802_) == 1 {
                                lean_dec(v___x_3801_);
                                v_val_3803_ = lean_ctor_get(v___x_3802_, 0);
                                lean_inc(v_val_3803_);
                                lean_dec_ref_known(v___x_3802_, 1);
                                v___x_3804_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_3804_, 0, v_val_3795_);
                                lean_ctor_set(v___x_3804_, 1, v_val_3799_);
                                lean_ctor_set(v___x_3804_, 2, v_val_3803_);
                                if v_isShared_3784_ == 0 {
                                    lean_ctor_set(v___x_3783_, 0, v___x_3804_);
                                    v___x_3806_ = v___x_3783_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3807_, 0, v___x_3804_);
                                    lean_ctor_set(v_reuseFailAlloc_3807_, 1, v_a_3781_);
                                    v___x_3806_ = v_reuseFailAlloc_3807_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_3802_);
                                lean_dec(v_val_3799_);
                                lean_dec(v_val_3795_);
                                lean_del_object(v___x_3783_);
                                v_str_3808_ = lean_ctor_get(v___x_3801_, 0);
                                lean_inc_ref(v_str_3808_);
                                v_startInclusive_3809_ = lean_ctor_get(v___x_3801_, 1);
                                lean_inc(v_startInclusive_3809_);
                                v_endExclusive_3810_ = lean_ctor_get(v___x_3801_, 2);
                                lean_inc(v_endExclusive_3810_);
                                lean_dec(v___x_3801_);
                                v___x_3811_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3;
                                v___x_3812_ = lean_string_utf8_extract(
                                    v_str_3808_,
                                    v_startInclusive_3809_,
                                    v_endExclusive_3810_,
                                );
                                lean_dec(v_endExclusive_3810_);
                                lean_dec(v_startInclusive_3809_);
                                lean_dec_ref(v_str_3808_);
                                v___x_3813_ = lean_string_append(v___x_3811_, v___x_3812_);
                                lean_dec_ref(v___x_3812_);
                                v___x_3814_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                v___x_3815_ = lean_string_append(v___x_3813_, v___x_3814_);
                                v_a_3772_ = v___x_3815_;
                                v_a_3773_ = v_a_3781_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_inc(v___x_3797_);
                            lean_dec(v___x_3798_);
                            lean_dec(v_val_3795_);
                            lean_del_object(v___x_3783_);
                            lean_dec(v_a_3780_);
                            v_str_3816_ = lean_ctor_get(v___x_3797_, 0);
                            lean_inc_ref(v_str_3816_);
                            v_startInclusive_3817_ = lean_ctor_get(v___x_3797_, 1);
                            lean_inc(v_startInclusive_3817_);
                            v_endExclusive_3818_ = lean_ctor_get(v___x_3797_, 2);
                            lean_inc(v_endExclusive_3818_);
                            lean_dec(v___x_3797_);
                            v___x_3819_ =
                                l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4;
                            v___x_3820_ = lean_string_utf8_extract(
                                v_str_3816_,
                                v_startInclusive_3817_,
                                v_endExclusive_3818_,
                            );
                            lean_dec(v_endExclusive_3818_);
                            lean_dec(v_startInclusive_3817_);
                            lean_dec_ref(v_str_3816_);
                            v___x_3821_ = lean_string_append(v___x_3819_, v___x_3820_);
                            lean_dec_ref(v___x_3820_);
                            v___x_3822_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                            v___x_3823_ = lean_string_append(v___x_3821_, v___x_3822_);
                            v_a_3772_ = v___x_3823_;
                            v_a_3773_ = v_a_3781_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_inc(v___x_3793_);
                        lean_dec(v___x_3794_);
                        lean_del_object(v___x_3783_);
                        lean_dec(v_a_3780_);
                        v_str_3824_ = lean_ctor_get(v___x_3793_, 0);
                        lean_inc_ref(v_str_3824_);
                        v_startInclusive_3825_ = lean_ctor_get(v___x_3793_, 1);
                        lean_inc(v_startInclusive_3825_);
                        v_endExclusive_3826_ = lean_ctor_get(v___x_3793_, 2);
                        lean_inc(v_endExclusive_3826_);
                        lean_dec(v___x_3793_);
                        v___x_3827_ =
                            l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5;
                        v___x_3828_ = lean_string_utf8_extract(
                            v_str_3824_,
                            v_startInclusive_3825_,
                            v_endExclusive_3826_,
                        );
                        lean_dec(v_endExclusive_3826_);
                        lean_dec(v_startInclusive_3825_);
                        lean_dec_ref(v_str_3824_);
                        v___x_3829_ = lean_string_append(v___x_3827_, v___x_3828_);
                        lean_dec_ref(v___x_3828_);
                        v___x_3830_ =
                            l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                        v___x_3831_ = lean_string_append(v___x_3829_, v___x_3830_);
                        v_a_3772_ = v___x_3831_;
                        v_a_3773_ = v_a_3781_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3806_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_SemVerCore_parse(mut v_s_3833_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    v___x_3834_ = lean_unsigned_to_nat(0);
    v___x_3835_ = lean_string_utf8_byte_size(v_s_3833_);
    lean_inc_ref(v_s_3833_);
    v___x_3836_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_3833_, v___x_3834_);
    if lean_obj_tag(v___x_3836_) == 0 {
        let mut v_a_3837_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_3838_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3839_: u8 = 0;
        v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
        lean_inc(v_a_3837_);
        v_a_3838_ = lean_ctor_get(v___x_3836_, 1);
        lean_inc(v_a_3838_);
        lean_dec_ref_known(v___x_3836_, 2);
        v___x_3839_ = lean_nat_dec_eq(v_a_3838_, v___x_3835_);
        if v___x_3839_ == 0 {
            let mut v_tail_3840_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_3837_);
            v_tail_3840_ = lean_string_utf8_extract(v_s_3833_, v_a_3838_, v___x_3835_);
            lean_dec(v_a_3838_);
            lean_dec_ref(v_s_3833_);
            v___x_3841_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0;
            v___x_3842_ = lean_string_append(v___x_3841_, v_tail_3840_);
            lean_dec_ref(v_tail_3840_);
            v___x_3843_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_3843_, 0, v___x_3842_);
            return v___x_3843_;
        } else {
            let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_3838_);
            lean_dec_ref(v_s_3833_);
            v___x_3844_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_3844_, 0, v_a_3837_);
            return v___x_3844_;
        }
    } else {
        let mut v_a_3845_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_3833_);
        v_a_3845_ = lean_ctor_get(v___x_3836_, 0);
        lean_inc(v_a_3845_);
        lean_dec_ref_known(v___x_3836_, 2);
        v___x_3846_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3846_, 0, v_a_3845_);
        return v___x_3846_;
    }
}
pub unsafe fn l_Lake_SemVerCore_toString(mut v_ver_3848_: *mut LeanObject) -> *mut LeanObject {
    let mut v_major_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minor_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_patch_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    v_major_3849_ = lean_ctor_get(v_ver_3848_, 0);
    lean_inc(v_major_3849_);
    v_minor_3850_ = lean_ctor_get(v_ver_3848_, 1);
    lean_inc(v_minor_3850_);
    v_patch_3851_ = lean_ctor_get(v_ver_3848_, 2);
    lean_inc(v_patch_3851_);
    lean_dec_ref(v_ver_3848_);
    v___x_3852_ = l_Nat_reprFast(v_major_3849_);
    v___x_3853_ = l_Lake_SemVerCore_toString___closed__0;
    v___x_3854_ = lean_string_append(v___x_3852_, v___x_3853_);
    v___x_3855_ = l_Nat_reprFast(v_minor_3850_);
    v___x_3856_ = lean_string_append(v___x_3854_, v___x_3855_);
    lean_dec_ref(v___x_3855_);
    v___x_3857_ = lean_string_append(v___x_3856_, v___x_3853_);
    v___x_3858_ = l_Nat_reprFast(v_patch_3851_);
    v___x_3859_ = lean_string_append(v___x_3857_, v___x_3858_);
    lean_dec_ref(v___x_3858_);
    return v___x_3859_;
}
pub unsafe fn l_Lake_SemVerCore_instToJson___lam__0(
    mut v_x_3862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    v___x_3863_ = l_Lake_SemVerCore_toString(v_x_3862_);
    v___x_3864_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3864_, 0, v___x_3863_);
    return v___x_3864_;
}
pub unsafe fn l_Lake_SemVerCore_instFromJson___lam__0(
    mut v_x_3867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3876_: u8 = 0;
    let mut v_a_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3868_ = l_Lean_Json_getStr_x3f(v_x_3867_);
                if lean_obj_tag(v___x_3868_) == 0 {
                    v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
                    v_isSharedCheck_3876_ = (!lean_is_exclusive(v___x_3868_)) as u8;
                    if v_isSharedCheck_3876_ == 0 {
                        v___x_3871_ = v___x_3868_;
                        v_isShared_3872_ = v_isSharedCheck_3876_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3869_);
                        lean_dec(v___x_3868_);
                        v___x_3871_ = lean_box(0);
                        v_isShared_3872_ = v_isSharedCheck_3876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3877_ = lean_ctor_get(v___x_3868_, 0);
                    lean_inc(v_a_3877_);
                    lean_dec_ref_known(v___x_3868_, 1);
                    v___x_3878_ = l_Lake_SemVerCore_parse(v_a_3877_);
                    return v___x_3878_;
                }
            }
            1 => {
                if v_isShared_3872_ == 0 {
                    v___x_3874_ = v___x_3871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3875_, 0, v_a_3869_);
                    v___x_3874_ = v_reuseFailAlloc_3875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_instReprStdVer_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    v___x_3895_ = lean_unsigned_to_nat(16);
    v___x_3896_ = lean_nat_to_int(v___x_3895_);
    return v___x_3896_;
}
pub unsafe fn l_Lake_instReprStdVer_repr___redArg(
    mut v_x_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemVerCore_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3905_: u8 = 0;
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: u8 = 0;
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSemVerCore_3901_ = lean_ctor_get(v_x_3900_, 0);
                v_specialDescr_3902_ = lean_ctor_get(v_x_3900_, 1);
                v_isSharedCheck_3935_ = (!lean_is_exclusive(v_x_3900_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v___x_3904_ = v_x_3900_;
                    v_isShared_3905_ = v_isSharedCheck_3935_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_specialDescr_3902_);
                    lean_inc(v_toSemVerCore_3901_);
                    lean_dec(v_x_3900_);
                    v___x_3904_ = lean_box(0);
                    v_isShared_3905_ = v_isSharedCheck_3935_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3906_ = l_Lake_instReprSemVerCore_repr___redArg___closed__5;
                v___x_3907_ = l_Lake_instReprStdVer_repr___redArg___closed__3;
                v___x_3908_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instReprStdVer_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(l_Lake_instReprStdVer_repr___redArg___closed__4_once),
                    _init_l_Lake_instReprStdVer_repr___redArg___closed__4,
                );
                v___x_3909_ = l_Lake_instReprSemVerCore_repr___redArg(v_toSemVerCore_3901_);
                if v_isShared_3905_ == 0 {
                    lean_ctor_set_tag(v___x_3904_, 4);
                    lean_ctor_set(v___x_3904_, 1, v___x_3909_);
                    lean_ctor_set(v___x_3904_, 0, v___x_3908_);
                    v___x_3911_ = v___x_3904_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3908_);
                    lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3909_);
                    v___x_3911_ = v_reuseFailAlloc_3934_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3912_ = 0;
                v___x_3913_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3913_, 0, v___x_3911_);
                lean_ctor_set_uint8(
                    v___x_3913_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3912_,
                );
                v___x_3914_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3914_, 0, v___x_3907_);
                lean_ctor_set(v___x_3914_, 1, v___x_3913_);
                v___x_3915_ = l_Lake_instReprSemVerCore_repr___redArg___closed__9;
                v___x_3916_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3916_, 0, v___x_3914_);
                lean_ctor_set(v___x_3916_, 1, v___x_3915_);
                v___x_3917_ = lean_box(1);
                v___x_3918_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3918_, 0, v___x_3916_);
                lean_ctor_set(v___x_3918_, 1, v___x_3917_);
                v___x_3919_ = l_Lake_instReprStdVer_repr___redArg___closed__6;
                v___x_3920_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3920_, 0, v___x_3918_);
                lean_ctor_set(v___x_3920_, 1, v___x_3919_);
                v___x_3921_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3921_, 0, v___x_3920_);
                lean_ctor_set(v___x_3921_, 1, v___x_3906_);
                v___x_3922_ = l_String_quote(v_specialDescr_3902_);
                v___x_3923_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_3923_, 0, v___x_3922_);
                v___x_3924_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3924_, 0, v___x_3908_);
                lean_ctor_set(v___x_3924_, 1, v___x_3923_);
                v___x_3925_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3925_, 0, v___x_3924_);
                lean_ctor_set_uint8(
                    v___x_3925_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3912_,
                );
                v___x_3926_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3926_, 0, v___x_3921_);
                lean_ctor_set(v___x_3926_, 1, v___x_3925_);
                v___x_3927_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__16),
                    core::ptr::addr_of_mut!(
                        l_Lake_instReprSemVerCore_repr___redArg___closed__16_once
                    ),
                    _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16,
                );
                v___x_3928_ = l_Lake_instReprSemVerCore_repr___redArg___closed__17;
                v___x_3929_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3929_, 0, v___x_3928_);
                lean_ctor_set(v___x_3929_, 1, v___x_3926_);
                v___x_3930_ = l_Lake_instReprSemVerCore_repr___redArg___closed__18;
                v___x_3931_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_3931_, 0, v___x_3929_);
                lean_ctor_set(v___x_3931_, 1, v___x_3930_);
                v___x_3932_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_3932_, 0, v___x_3927_);
                lean_ctor_set(v___x_3932_, 1, v___x_3931_);
                v___x_3933_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_3933_, 0, v___x_3932_);
                lean_ctor_set_uint8(
                    v___x_3933_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3912_,
                );
                return v___x_3933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprStdVer_repr(
    mut v_x_3936_: *mut LeanObject,
    mut v_prec_3937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    v___x_3938_ = l_Lake_instReprStdVer_repr___redArg(v_x_3936_);
    return v___x_3938_;
}
pub unsafe fn l_Lake_instReprStdVer_repr___boxed(
    mut v_x_3939_: *mut LeanObject,
    mut v_prec_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3941_: *mut LeanObject = core::ptr::null_mut();
    v_res_3941_ = l_Lake_instReprStdVer_repr(v_x_3939_, v_prec_3940_);
    lean_dec(v_prec_3940_);
    return v_res_3941_;
}
pub unsafe fn l_Lake_instDecidableEqStdVer_decEq(
    mut v_x_3944_: *mut LeanObject,
    mut v_x_3945_: *mut LeanObject,
) -> u8 {
    let mut v_toSemVerCore_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSemVerCore_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: u8 = 0;
    v_toSemVerCore_3946_ = lean_ctor_get(v_x_3944_, 0);
    v_specialDescr_3947_ = lean_ctor_get(v_x_3944_, 1);
    v_toSemVerCore_3948_ = lean_ctor_get(v_x_3945_, 0);
    v_specialDescr_3949_ = lean_ctor_get(v_x_3945_, 1);
    v___x_3950_ =
        l_Lake_instDecidableEqSemVerCore_decEq(v_toSemVerCore_3946_, v_toSemVerCore_3948_);
    if v___x_3950_ == 0 {
        return v___x_3950_;
    } else {
        let mut v___x_3951_: u8 = 0;
        v___x_3951_ = lean_string_dec_eq(v_specialDescr_3947_, v_specialDescr_3949_);
        return v___x_3951_;
    }
}
pub unsafe fn l_Lake_instDecidableEqStdVer_decEq___boxed(
    mut v_x_3952_: *mut LeanObject,
    mut v_x_3953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3954_: u8 = 0;
    let mut v_r_3955_: *mut LeanObject = core::ptr::null_mut();
    v_res_3954_ = l_Lake_instDecidableEqStdVer_decEq(v_x_3952_, v_x_3953_);
    lean_dec_ref(v_x_3953_);
    lean_dec_ref(v_x_3952_);
    v_r_3955_ = lean_box((v_res_3954_) as usize);
    return v_r_3955_;
}
pub unsafe fn l_Lake_instDecidableEqStdVer(
    mut v_x_3956_: *mut LeanObject,
    mut v_x_3957_: *mut LeanObject,
) -> u8 {
    let mut v___x_3958_: u8 = 0;
    v___x_3958_ = l_Lake_instDecidableEqStdVer_decEq(v_x_3956_, v_x_3957_);
    return v___x_3958_;
}
pub unsafe fn l_Lake_instDecidableEqStdVer___boxed(
    mut v_x_3959_: *mut LeanObject,
    mut v_x_3960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3961_: u8 = 0;
    let mut v_r_3962_: *mut LeanObject = core::ptr::null_mut();
    v_res_3961_ = l_Lake_instDecidableEqStdVer(v_x_3959_, v_x_3960_);
    lean_dec_ref(v_x_3960_);
    lean_dec_ref(v_x_3959_);
    v_r_3962_ = lean_box((v_res_3961_) as usize);
    return v_r_3962_;
}
pub unsafe fn l_Lake_StdVer_instCoeSemVerCore___lam__0(
    mut v_self_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemVerCore_3964_: *mut LeanObject = core::ptr::null_mut();
    v_toSemVerCore_3964_ = lean_ctor_get(v_self_3963_, 0);
    lean_inc_ref(v_toSemVerCore_3964_);
    return v_toSemVerCore_3964_;
}
pub unsafe fn l_Lake_StdVer_instCoeSemVerCore___lam__0___boxed(
    mut v_self_3965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3966_: *mut LeanObject = core::ptr::null_mut();
    v_res_3966_ = l_Lake_StdVer_instCoeSemVerCore___lam__0(v_self_3965_);
    lean_dec_ref(v_self_3965_);
    return v_res_3966_;
}
pub unsafe fn l_Lake_StdVer_ofSemVerCore(mut v_ver_3969_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    v___x_3970_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
    v___x_3971_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3971_, 0, v_ver_3969_);
    lean_ctor_set(v___x_3971_, 1, v___x_3970_);
    return v___x_3971_;
}
pub unsafe fn l_Lake_StdVer_compare(
    mut v_a_3974_: *mut LeanObject,
    mut v_b_3975_: *mut LeanObject,
) -> u8 {
    let mut v_toSemVerCore_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSemVerCore_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: u8 = 0;
    v_toSemVerCore_3976_ = lean_ctor_get(v_a_3974_, 0);
    v_specialDescr_3977_ = lean_ctor_get(v_a_3974_, 1);
    v_toSemVerCore_3978_ = lean_ctor_get(v_b_3975_, 0);
    v_specialDescr_3979_ = lean_ctor_get(v_b_3975_, 1);
    v___x_3980_ = l_Lake_instOrdSemVerCore_ord(v_toSemVerCore_3976_, v_toSemVerCore_3978_);
    if v___x_3980_ == 1 {
        let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3982_: u8 = 0;
        v___x_3981_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
        v___x_3982_ = lean_string_dec_eq(v_specialDescr_3977_, v___x_3981_);
        if v___x_3982_ == 0 {
            let mut v___x_3983_: u8 = 0;
            v___x_3983_ = lean_string_dec_eq(v_specialDescr_3979_, v___x_3981_);
            if v___x_3983_ == 0 {
                let mut v___x_3984_: u8 = 0;
                v___x_3984_ = lean_string_compare(v_specialDescr_3977_, v_specialDescr_3979_);
                return v___x_3984_;
            } else {
                let mut v___x_3985_: u8 = 0;
                v___x_3985_ = 0;
                return v___x_3985_;
            }
        } else {
            let mut v___x_3986_: u8 = 0;
            v___x_3986_ = lean_string_dec_eq(v_specialDescr_3979_, v___x_3981_);
            if v___x_3986_ == 0 {
                let mut v___x_3987_: u8 = 0;
                v___x_3987_ = 2;
                return v___x_3987_;
            } else {
                return v___x_3980_;
            }
        }
    } else {
        return v___x_3980_;
    }
}
pub unsafe fn l_Lake_StdVer_compare___boxed(
    mut v_a_3988_: *mut LeanObject,
    mut v_b_3989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3990_: u8 = 0;
    let mut v_r_3991_: *mut LeanObject = core::ptr::null_mut();
    v_res_3990_ = l_Lake_StdVer_compare(v_a_3988_, v_b_3989_);
    lean_dec_ref(v_b_3989_);
    lean_dec_ref(v_a_3988_);
    v_r_3991_ = lean_box((v_res_3990_) as usize);
    return v_r_3991_;
}
pub unsafe fn _init_l_Lake_StdVer_instLT() -> *mut LeanObject {
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    v___x_3994_ = lean_box(0);
    return v___x_3994_;
}
pub unsafe fn _init_l_Lake_StdVer_instLE() -> *mut LeanObject {
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    v___x_3995_ = lean_box(0);
    return v___x_3995_;
}
pub unsafe fn l_Lake_StdVer_instMin___lam__0(
    mut v_x_3996_: *mut LeanObject,
    mut v_y_3997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3998_: u8 = 0;
    v___x_3998_ = l_Lake_StdVer_compare(v_x_3996_, v_y_3997_);
    if v___x_3998_ == 2 {
        lean_inc_ref(v_y_3997_);
        return v_y_3997_;
    } else {
        lean_inc_ref(v_x_3996_);
        return v_x_3996_;
    }
}
pub unsafe fn l_Lake_StdVer_instMin___lam__0___boxed(
    mut v_x_3999_: *mut LeanObject,
    mut v_y_4000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4001_: *mut LeanObject = core::ptr::null_mut();
    v_res_4001_ = l_Lake_StdVer_instMin___lam__0(v_x_3999_, v_y_4000_);
    lean_dec_ref(v_y_4000_);
    lean_dec_ref(v_x_3999_);
    return v_res_4001_;
}
pub unsafe fn l_Lake_StdVer_instMax___lam__0(
    mut v_x_4004_: *mut LeanObject,
    mut v_y_4005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4006_: u8 = 0;
    v___x_4006_ = l_Lake_StdVer_compare(v_x_4004_, v_y_4005_);
    if v___x_4006_ == 2 {
        lean_inc_ref(v_x_4004_);
        return v_x_4004_;
    } else {
        lean_inc_ref(v_y_4005_);
        return v_y_4005_;
    }
}
pub unsafe fn l_Lake_StdVer_instMax___lam__0___boxed(
    mut v_x_4007_: *mut LeanObject,
    mut v_y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4009_: *mut LeanObject = core::ptr::null_mut();
    v_res_4009_ = l_Lake_StdVer_instMax___lam__0(v_x_4007_, v_y_4008_);
    lean_dec_ref(v_y_4008_);
    lean_dec_ref(v_x_4007_);
    return v_res_4009_;
}
pub unsafe fn l_Lake_StdVer_parseM(
    mut v_s_4012_: *mut LeanObject,
    mut v_a_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4027_: u8 = 0;
    let mut v_a_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4032_: u8 = 0;
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4036_: u8 = 0;
    let mut v_a_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4041_: u8 = 0;
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_s_4012_);
                v___x_4014_ =
                    l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(v_s_4012_, v_a_4013_);
                if lean_obj_tag(v___x_4014_) == 0 {
                    v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
                    lean_inc(v_a_4015_);
                    v_a_4016_ = lean_ctor_get(v___x_4014_, 1);
                    lean_inc(v_a_4016_);
                    lean_dec_ref_known(v___x_4014_, 2);
                    v___x_4017_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(
                        v_s_4012_, v_a_4016_,
                    );
                    lean_dec_ref(v_s_4012_);
                    if lean_obj_tag(v___x_4017_) == 0 {
                        v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
                        v_a_4019_ = lean_ctor_get(v___x_4017_, 1);
                        v_isSharedCheck_4027_ = (!lean_is_exclusive(v___x_4017_)) as u8;
                        if v_isSharedCheck_4027_ == 0 {
                            v___x_4021_ = v___x_4017_;
                            v_isShared_4022_ = v_isSharedCheck_4027_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4019_);
                            lean_inc(v_a_4018_);
                            lean_dec(v___x_4017_);
                            v___x_4021_ = lean_box(0);
                            v_isShared_4022_ = v_isSharedCheck_4027_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4015_);
                        v_a_4028_ = lean_ctor_get(v___x_4017_, 0);
                        v_a_4029_ = lean_ctor_get(v___x_4017_, 1);
                        v_isSharedCheck_4036_ = (!lean_is_exclusive(v___x_4017_)) as u8;
                        if v_isSharedCheck_4036_ == 0 {
                            v___x_4031_ = v___x_4017_;
                            v_isShared_4032_ = v_isSharedCheck_4036_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4029_);
                            lean_inc(v_a_4028_);
                            lean_dec(v___x_4017_);
                            v___x_4031_ = lean_box(0);
                            v_isShared_4032_ = v_isSharedCheck_4036_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_s_4012_);
                    v_a_4037_ = lean_ctor_get(v___x_4014_, 0);
                    v_a_4038_ = lean_ctor_get(v___x_4014_, 1);
                    v_isSharedCheck_4045_ = (!lean_is_exclusive(v___x_4014_)) as u8;
                    if v_isSharedCheck_4045_ == 0 {
                        v___x_4040_ = v___x_4014_;
                        v_isShared_4041_ = v_isSharedCheck_4045_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4038_);
                        lean_inc(v_a_4037_);
                        lean_dec(v___x_4014_);
                        v___x_4040_ = lean_box(0);
                        v_isShared_4041_ = v_isSharedCheck_4045_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4023_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4023_, 0, v_a_4015_);
                lean_ctor_set(v___x_4023_, 1, v_a_4018_);
                if v_isShared_4022_ == 0 {
                    lean_ctor_set(v___x_4021_, 0, v___x_4023_);
                    v___x_4025_ = v___x_4021_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4026_, 0, v___x_4023_);
                    lean_ctor_set(v_reuseFailAlloc_4026_, 1, v_a_4019_);
                    v___x_4025_ = v_reuseFailAlloc_4026_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4025_;
            }
            3 => {
                if v_isShared_4032_ == 0 {
                    v___x_4034_ = v___x_4031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4028_);
                    lean_ctor_set(v_reuseFailAlloc_4035_, 1, v_a_4029_);
                    v___x_4034_ = v_reuseFailAlloc_4035_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4034_;
            }
            5 => {
                if v_isShared_4041_ == 0 {
                    v___x_4043_ = v___x_4040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4037_);
                    lean_ctor_set(v_reuseFailAlloc_4044_, 1, v_a_4038_);
                    v___x_4043_ = v_reuseFailAlloc_4044_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_StdVer_parse(mut v_s_4046_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    v___x_4047_ = lean_unsigned_to_nat(0);
    v___x_4048_ = lean_string_utf8_byte_size(v_s_4046_);
    lean_inc_ref(v_s_4046_);
    v___x_4049_ = l_Lake_StdVer_parseM(v_s_4046_, v___x_4047_);
    if lean_obj_tag(v___x_4049_) == 0 {
        let mut v_a_4050_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_4051_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4052_: u8 = 0;
        v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
        lean_inc(v_a_4050_);
        v_a_4051_ = lean_ctor_get(v___x_4049_, 1);
        lean_inc(v_a_4051_);
        lean_dec_ref_known(v___x_4049_, 2);
        v___x_4052_ = lean_nat_dec_eq(v_a_4051_, v___x_4048_);
        if v___x_4052_ == 0 {
            let mut v_tail_4053_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_4050_);
            v_tail_4053_ = lean_string_utf8_extract(v_s_4046_, v_a_4051_, v___x_4048_);
            lean_dec(v_a_4051_);
            lean_dec_ref(v_s_4046_);
            v___x_4054_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0;
            v___x_4055_ = lean_string_append(v___x_4054_, v_tail_4053_);
            lean_dec_ref(v_tail_4053_);
            v___x_4056_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_4056_, 0, v___x_4055_);
            return v___x_4056_;
        } else {
            let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_4051_);
            lean_dec_ref(v_s_4046_);
            v___x_4057_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4057_, 0, v_a_4050_);
            return v___x_4057_;
        }
    } else {
        let mut v_a_4058_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_4046_);
        v_a_4058_ = lean_ctor_get(v___x_4049_, 0);
        lean_inc(v_a_4058_);
        lean_dec_ref_known(v___x_4049_, 2);
        v___x_4059_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4059_, 0, v_a_4058_);
        return v___x_4059_;
    }
}
pub unsafe fn l_Lake_StdVer_toString(mut v_ver_4061_: *mut LeanObject) -> *mut LeanObject {
    let mut v_toSemVerCore_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    v_toSemVerCore_4062_ = lean_ctor_get(v_ver_4061_, 0);
    lean_inc_ref(v_toSemVerCore_4062_);
    v_specialDescr_4063_ = lean_ctor_get(v_ver_4061_, 1);
    lean_inc_ref(v_specialDescr_4063_);
    lean_dec_ref(v_ver_4061_);
    v___x_4064_ = lean_string_utf8_byte_size(v_specialDescr_4063_);
    v___x_4065_ = lean_unsigned_to_nat(0);
    v___x_4066_ = lean_nat_dec_eq(v___x_4064_, v___x_4065_);
    if v___x_4066_ == 0 {
        let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
        v___x_4067_ = l_Lake_SemVerCore_toString(v_toSemVerCore_4062_);
        v___x_4068_ = l_Lake_StdVer_toString___closed__0;
        v___x_4069_ = lean_string_append(v___x_4067_, v___x_4068_);
        v___x_4070_ = lean_string_append(v___x_4069_, v_specialDescr_4063_);
        lean_dec_ref(v_specialDescr_4063_);
        return v___x_4070_;
    } else {
        let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_specialDescr_4063_);
        v___x_4071_ = l_Lake_SemVerCore_toString(v_toSemVerCore_4062_);
        return v___x_4071_;
    }
}
pub unsafe fn l_Lake_StdVer_instToJson___lam__0(mut v_x_4074_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    v___x_4075_ = l_Lake_StdVer_toString(v_x_4074_);
    v___x_4076_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4076_, 0, v___x_4075_);
    return v___x_4076_;
}
pub unsafe fn l_Lake_StdVer_instFromJson___lam__0(
    mut v_x_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4084_: u8 = 0;
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4088_: u8 = 0;
    let mut v_a_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4080_ = l_Lean_Json_getStr_x3f(v_x_4079_);
                if lean_obj_tag(v___x_4080_) == 0 {
                    v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
                    v_isSharedCheck_4088_ = (!lean_is_exclusive(v___x_4080_)) as u8;
                    if v_isSharedCheck_4088_ == 0 {
                        v___x_4083_ = v___x_4080_;
                        v_isShared_4084_ = v_isSharedCheck_4088_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4081_);
                        lean_dec(v___x_4080_);
                        v___x_4083_ = lean_box(0);
                        v_isShared_4084_ = v_isSharedCheck_4088_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4089_ = lean_ctor_get(v___x_4080_, 0);
                    lean_inc(v_a_4089_);
                    lean_dec_ref_known(v___x_4080_, 1);
                    v___x_4090_ = l_Lake_StdVer_parse(v_a_4089_);
                    return v___x_4090_;
                }
            }
            1 => {
                if v_isShared_4084_ == 0 {
                    v___x_4086_ = v___x_4083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
                    v___x_4086_ = v_reuseFailAlloc_4087_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_ctorIdx(mut v_x_4099_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_4099_) {
        0 => {
            let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
            v___x_4100_ = lean_unsigned_to_nat(0);
            return v___x_4100_;
        }
        1 => {
            let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
            v___x_4101_ = lean_unsigned_to_nat(1);
            return v___x_4101_;
        }
        2 => {
            let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
            v___x_4102_ = lean_unsigned_to_nat(2);
            return v___x_4102_;
        }
        _ => {
            let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
            v___x_4103_ = lean_unsigned_to_nat(3);
            return v___x_4103_;
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_ctorIdx___boxed(
    mut v_x_4104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4105_: *mut LeanObject = core::ptr::null_mut();
    v_res_4105_ = l_Lake_ToolchainVer_ctorIdx(v_x_4104_);
    lean_dec_ref(v_x_4104_);
    return v_res_4105_;
}
pub unsafe fn l_Lake_ToolchainVer_ctorElim___redArg(
    mut v_t_4106_: *mut LeanObject,
    mut v_k_4107_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4106_) {
        1 => {
            let mut v_date_4108_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rev_4109_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
            v_date_4108_ = lean_ctor_get(v_t_4106_, 0);
            lean_inc_ref(v_date_4108_);
            v_rev_4109_ = lean_ctor_get(v_t_4106_, 1);
            lean_inc(v_rev_4109_);
            lean_dec_ref_known(v_t_4106_, 2);
            v___x_4110_ = lean_apply_2(v_k_4107_, v_date_4108_, v_rev_4109_);
            return v___x_4110_;
        }
        2 => {
            let mut v_n_4111_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
            v_n_4111_ = lean_ctor_get(v_t_4106_, 0);
            lean_inc(v_n_4111_);
            lean_dec_ref_known(v_t_4106_, 1);
            v___x_4112_ = lean_apply_1(v_k_4107_, v_n_4111_);
            return v___x_4112_;
        }
        _ => {
            let mut v_ver_4113_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
            v_ver_4113_ = lean_ctor_get(v_t_4106_, 0);
            lean_inc_ref(v_ver_4113_);
            lean_dec_ref(v_t_4106_);
            v___x_4114_ = lean_apply_1(v_k_4107_, v_ver_4113_);
            return v___x_4114_;
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_ctorElim(
    mut v_motive_4115_: *mut LeanObject,
    mut v_ctorIdx_4116_: *mut LeanObject,
    mut v_t_4117_: *mut LeanObject,
    mut v_h_4118_: *mut LeanObject,
    mut v_k_4119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    v___x_4120_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4117_, v_k_4119_);
    return v___x_4120_;
}
pub unsafe fn l_Lake_ToolchainVer_ctorElim___boxed(
    mut v_motive_4121_: *mut LeanObject,
    mut v_ctorIdx_4122_: *mut LeanObject,
    mut v_t_4123_: *mut LeanObject,
    mut v_h_4124_: *mut LeanObject,
    mut v_k_4125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4126_: *mut LeanObject = core::ptr::null_mut();
    v_res_4126_ = l_Lake_ToolchainVer_ctorElim(
        v_motive_4121_,
        v_ctorIdx_4122_,
        v_t_4123_,
        v_h_4124_,
        v_k_4125_,
    );
    lean_dec(v_ctorIdx_4122_);
    return v_res_4126_;
}
pub unsafe fn l_Lake_ToolchainVer_release_elim___redArg(
    mut v_t_4127_: *mut LeanObject,
    mut v_release_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    v___x_4129_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4127_, v_release_4128_);
    return v___x_4129_;
}
pub unsafe fn l_Lake_ToolchainVer_release_elim(
    mut v_motive_4130_: *mut LeanObject,
    mut v_t_4131_: *mut LeanObject,
    mut v_h_4132_: *mut LeanObject,
    mut v_release_4133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    v___x_4134_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4131_, v_release_4133_);
    return v___x_4134_;
}
pub unsafe fn l_Lake_ToolchainVer_nightly_elim___redArg(
    mut v_t_4135_: *mut LeanObject,
    mut v_nightly_4136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4135_, v_nightly_4136_);
    return v___x_4137_;
}
pub unsafe fn l_Lake_ToolchainVer_nightly_elim(
    mut v_motive_4138_: *mut LeanObject,
    mut v_t_4139_: *mut LeanObject,
    mut v_h_4140_: *mut LeanObject,
    mut v_nightly_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4139_, v_nightly_4141_);
    return v___x_4142_;
}
pub unsafe fn l_Lake_ToolchainVer_pr_elim___redArg(
    mut v_t_4143_: *mut LeanObject,
    mut v_pr_4144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    v___x_4145_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4143_, v_pr_4144_);
    return v___x_4145_;
}
pub unsafe fn l_Lake_ToolchainVer_pr_elim(
    mut v_motive_4146_: *mut LeanObject,
    mut v_t_4147_: *mut LeanObject,
    mut v_h_4148_: *mut LeanObject,
    mut v_pr_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    v___x_4150_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4147_, v_pr_4149_);
    return v___x_4150_;
}
pub unsafe fn l_Lake_ToolchainVer_other_elim___redArg(
    mut v_t_4151_: *mut LeanObject,
    mut v_other_4152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    v___x_4153_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4151_, v_other_4152_);
    return v___x_4153_;
}
pub unsafe fn l_Lake_ToolchainVer_other_elim(
    mut v_motive_4154_: *mut LeanObject,
    mut v_t_4155_: *mut LeanObject,
    mut v_h_4156_: *mut LeanObject,
    mut v_other_4157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    v___x_4158_ = l_Lake_ToolchainVer_ctorElim___redArg(v_t_4155_, v_other_4157_);
    return v___x_4158_;
}
pub unsafe fn l_Lake_ToolchainVer_casesOn___override___redArg(
    mut v_t_4159_: *mut LeanObject,
    mut v_release_4160_: *mut LeanObject,
    mut v_nightly_4161_: *mut LeanObject,
    mut v_pr_4162_: *mut LeanObject,
    mut v_other_4163_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4159_) {
        0 => {
            let mut v_ver_4164_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_other_4163_);
            lean_dec(v_pr_4162_);
            lean_dec(v_nightly_4161_);
            v_ver_4164_ = lean_ctor_get(v_t_4159_, 1);
            lean_inc_ref(v_ver_4164_);
            lean_dec_ref_known(v_t_4159_, 2);
            v___x_4165_ = lean_apply_1(v_release_4160_, v_ver_4164_);
            return v___x_4165_;
        }
        1 => {
            let mut v_date_4166_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rev_4167_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_other_4163_);
            lean_dec(v_pr_4162_);
            lean_dec(v_release_4160_);
            v_date_4166_ = lean_ctor_get(v_t_4159_, 1);
            lean_inc_ref(v_date_4166_);
            v_rev_4167_ = lean_ctor_get(v_t_4159_, 2);
            lean_inc(v_rev_4167_);
            lean_dec_ref_known(v_t_4159_, 3);
            v___x_4168_ = lean_apply_2(v_nightly_4161_, v_date_4166_, v_rev_4167_);
            return v___x_4168_;
        }
        2 => {
            let mut v_n_4169_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_other_4163_);
            lean_dec(v_nightly_4161_);
            lean_dec(v_release_4160_);
            v_n_4169_ = lean_ctor_get(v_t_4159_, 1);
            lean_inc(v_n_4169_);
            lean_dec_ref_known(v_t_4159_, 2);
            v___x_4170_ = lean_apply_1(v_pr_4162_, v_n_4169_);
            return v___x_4170_;
        }
        _ => {
            let mut v_v_4171_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_pr_4162_);
            lean_dec(v_nightly_4161_);
            lean_dec(v_release_4160_);
            v_v_4171_ = lean_ctor_get(v_t_4159_, 1);
            lean_inc_ref(v_v_4171_);
            lean_dec_ref_known(v_t_4159_, 2);
            v___x_4172_ = lean_apply_1(v_other_4163_, v_v_4171_);
            return v___x_4172_;
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_casesOn___override(
    mut v_motive_4173_: *mut LeanObject,
    mut v_t_4174_: *mut LeanObject,
    mut v_release_4175_: *mut LeanObject,
    mut v_nightly_4176_: *mut LeanObject,
    mut v_pr_4177_: *mut LeanObject,
    mut v_other_4178_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_4174_) {
        0 => {
            let mut v_ver_4179_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_other_4178_);
            lean_dec(v_pr_4177_);
            lean_dec(v_nightly_4176_);
            v_ver_4179_ = lean_ctor_get(v_t_4174_, 1);
            lean_inc_ref(v_ver_4179_);
            lean_dec_ref_known(v_t_4174_, 2);
            v___x_4180_ = lean_apply_1(v_release_4175_, v_ver_4179_);
            return v___x_4180_;
        }
        1 => {
            let mut v_date_4181_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rev_4182_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_other_4178_);
            lean_dec(v_pr_4177_);
            lean_dec(v_release_4175_);
            v_date_4181_ = lean_ctor_get(v_t_4174_, 1);
            lean_inc_ref(v_date_4181_);
            v_rev_4182_ = lean_ctor_get(v_t_4174_, 2);
            lean_inc(v_rev_4182_);
            lean_dec_ref_known(v_t_4174_, 3);
            v___x_4183_ = lean_apply_2(v_nightly_4176_, v_date_4181_, v_rev_4182_);
            return v___x_4183_;
        }
        2 => {
            let mut v_n_4184_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_other_4178_);
            lean_dec(v_nightly_4176_);
            lean_dec(v_release_4175_);
            v_n_4184_ = lean_ctor_get(v_t_4174_, 1);
            lean_inc(v_n_4184_);
            lean_dec_ref_known(v_t_4174_, 2);
            v___x_4185_ = lean_apply_1(v_pr_4177_, v_n_4184_);
            return v___x_4185_;
        }
        _ => {
            let mut v_v_4186_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_pr_4177_);
            lean_dec(v_nightly_4176_);
            lean_dec(v_release_4175_);
            v_v_4186_ = lean_ctor_get(v_t_4174_, 1);
            lean_inc_ref(v_v_4186_);
            lean_dec_ref_known(v_t_4174_, 2);
            v___x_4187_ = lean_apply_1(v_other_4178_, v_v_4186_);
            return v___x_4187_;
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_release___override(
    mut v_ver_4189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    v___x_4190_ = l_Lake_ToolchainVer_release___override___closed__0;
    lean_inc_ref(v_ver_4189_);
    v___x_4191_ = l_Lake_StdVer_toString(v_ver_4189_);
    v___x_4192_ = lean_string_append(v___x_4190_, v___x_4191_);
    lean_dec_ref(v___x_4191_);
    v___x_4193_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4193_, 0, v___x_4192_);
    lean_ctor_set(v___x_4193_, 1, v_ver_4189_);
    return v___x_4193_;
}
pub unsafe fn l_Lake_ToolchainVer_nightly___override(
    mut v_date_4196_: *mut LeanObject,
    mut v_rev_4197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4198_ = l_Lake_ToolchainVer_nightly___override___closed__0;
                lean_inc_ref(v_date_4196_);
                v___x_4199_ = l_Lake_Date_toString(v_date_4196_);
                v___x_4200_ = lean_string_append(v___x_4198_, v___x_4199_);
                lean_dec_ref(v___x_4199_);
                if lean_obj_tag(v_rev_4197_) == 0 {
                    v___x_4205_ =
                        l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                    v___y_4202_ = v___x_4205_;
                    state = 1;
                    continue;
                } else {
                    v_val_4206_ = lean_ctor_get(v_rev_4197_, 0);
                    v___x_4207_ = l_Lake_ToolchainVer_nightly___override___closed__1;
                    lean_inc(v_val_4206_);
                    v___x_4208_ = l_Nat_reprFast(v_val_4206_);
                    v___x_4209_ = lean_string_append(v___x_4207_, v___x_4208_);
                    lean_dec_ref(v___x_4208_);
                    v___y_4202_ = v___x_4209_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4203_ = lean_string_append(v___x_4200_, v___y_4202_);
                lean_dec_ref(v___y_4202_);
                v___x_4204_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4204_, 0, v___x_4203_);
                lean_ctor_set(v___x_4204_, 1, v_date_4196_);
                lean_ctor_set(v___x_4204_, 2, v_rev_4197_);
                return v___x_4204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_pr___override(mut v_n_4211_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    v___x_4212_ = l_Lake_ToolchainVer_pr___override___closed__0;
    lean_inc(v_n_4211_);
    v___x_4213_ = l_Nat_reprFast(v_n_4211_);
    v___x_4214_ = lean_string_append(v___x_4212_, v___x_4213_);
    lean_dec_ref(v___x_4213_);
    v___x_4215_ = lean_alloc_ctor(2, 2, (0) as u32);
    lean_ctor_set(v___x_4215_, 0, v___x_4214_);
    lean_ctor_set(v___x_4215_, 1, v_n_4211_);
    return v___x_4215_;
}
pub unsafe fn l_Lake_ToolchainVer_other___override(
    mut v_v_4216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_v_4216_);
    v___x_4217_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4217_, 0, v_v_4216_);
    lean_ctor_set(v___x_4217_, 1, v_v_4216_);
    return v___x_4217_;
}
pub unsafe fn l_Lake_ToolchainVer_toString___override(
    mut v_x_4218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toString_4219_: *mut LeanObject = core::ptr::null_mut();
    v_toString_4219_ = lean_ctor_get(v_x_4218_, 0);
    lean_inc_ref(v_toString_4219_);
    return v_toString_4219_;
}
pub unsafe fn l_Lake_ToolchainVer_toString___override___boxed(
    mut v_x_4220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4221_: *mut LeanObject = core::ptr::null_mut();
    v_res_4221_ = l_Lake_ToolchainVer_toString___override(v_x_4220_);
    lean_dec_ref(v_x_4220_);
    return v_res_4221_;
}
pub unsafe fn l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(
    mut v_x_4228_: *mut LeanObject,
    mut v_x_4229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4242_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4228_) == 0 {
                    v___x_4230_ =
                        l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__1;
                    return v___x_4230_;
                } else {
                    v_val_4231_ = lean_ctor_get(v_x_4228_, 0);
                    v_isSharedCheck_4242_ = (!lean_is_exclusive(v_x_4228_)) as u8;
                    if v_isSharedCheck_4242_ == 0 {
                        v___x_4233_ = v_x_4228_;
                        v_isShared_4234_ = v_isSharedCheck_4242_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4231_);
                        lean_dec(v_x_4228_);
                        v___x_4233_ = lean_box(0);
                        v_isShared_4234_ = v_isSharedCheck_4242_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4235_ =
                    l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___closed__3;
                v___x_4236_ = l_Nat_reprFast(v_val_4231_);
                if v_isShared_4234_ == 0 {
                    lean_ctor_set_tag(v___x_4233_, 3);
                    lean_ctor_set(v___x_4233_, 0, v___x_4236_);
                    v___x_4238_ = v___x_4233_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4241_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4236_);
                    v___x_4238_ = v_reuseFailAlloc_4241_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4239_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4239_, 0, v___x_4235_);
                lean_ctor_set(v___x_4239_, 1, v___x_4238_);
                v___x_4240_ = l_Repr_addAppParen(v___x_4239_, v_x_4229_);
                return v___x_4240_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0___boxed(
    mut v_x_4243_: *mut LeanObject,
    mut v_x_4244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4245_: *mut LeanObject = core::ptr::null_mut();
    v_res_4245_ =
        l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(v_x_4243_, v_x_4244_);
    lean_dec(v_x_4244_);
    return v_res_4245_;
}
pub unsafe fn _init_l_Lake_instReprToolchainVer_repr___closed__3() -> *mut LeanObject {
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    v___x_4252_ = lean_unsigned_to_nat(2);
    v___x_4253_ = lean_nat_to_int(v___x_4252_);
    return v___x_4253_;
}
pub unsafe fn _init_l_Lake_instReprToolchainVer_repr___closed__4() -> *mut LeanObject {
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    v___x_4254_ = lean_unsigned_to_nat(1);
    v___x_4255_ = lean_nat_to_int(v___x_4254_);
    return v___x_4255_;
}
pub unsafe fn l_Lake_instReprToolchainVer_repr(
    mut v_x_4274_: *mut LeanObject,
    mut v_prec_4275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ver_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4279_: u8 = 0;
    let mut v___y_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: u8 = 0;
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: u8 = 0;
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4295_: u8 = 0;
    let mut v_unused_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: u8 = 0;
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4320_: u8 = 0;
    let mut v___y_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: u8 = 0;
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v_unused_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___y_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: u8 = 0;
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4359_: u8 = 0;
    let mut v_unused_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_4274_) {
                0 => {
                    v_ver_4276_ = lean_ctor_get(v_x_4274_, 1);
                    v_isSharedCheck_4295_ = (!lean_is_exclusive(v_x_4274_)) as u8;
                    if v_isSharedCheck_4295_ == 0 {
                        v_unused_4296_ = lean_ctor_get(v_x_4274_, 0);
                        lean_dec(v_unused_4296_);
                        v___x_4278_ = v_x_4274_;
                        v_isShared_4279_ = v_isSharedCheck_4295_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_ver_4276_);
                        lean_dec(v_x_4274_);
                        v___x_4278_ = lean_box(0);
                        v_isShared_4279_ = v_isSharedCheck_4295_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_date_4297_ = lean_ctor_get(v_x_4274_, 1);
                    lean_inc_ref(v_date_4297_);
                    v_rev_4298_ = lean_ctor_get(v_x_4274_, 2);
                    lean_inc(v_rev_4298_);
                    lean_dec_ref_known(v_x_4274_, 3);
                    v___x_4313_ = lean_unsigned_to_nat(1024);
                    v___x_4314_ = lean_nat_dec_le(v___x_4313_, v_prec_4275_);
                    if v___x_4314_ == 0 {
                        v___x_4315_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__3,
                        );
                        v___y_4300_ = v___x_4315_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4316_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__4,
                        );
                        v___y_4300_ = v___x_4316_;
                        state = 4;
                        continue;
                    }
                }
                2 => {
                    v_n_4317_ = lean_ctor_get(v_x_4274_, 1);
                    v_isSharedCheck_4337_ = (!lean_is_exclusive(v_x_4274_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v_unused_4338_ = lean_ctor_get(v_x_4274_, 0);
                        lean_dec(v_unused_4338_);
                        v___x_4319_ = v_x_4274_;
                        v_isShared_4320_ = v_isSharedCheck_4337_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_n_4317_);
                        lean_dec(v_x_4274_);
                        v___x_4319_ = lean_box(0);
                        v_isShared_4320_ = v_isSharedCheck_4337_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_v_4339_ = lean_ctor_get(v_x_4274_, 1);
                    v_isSharedCheck_4359_ = (!lean_is_exclusive(v_x_4274_)) as u8;
                    if v_isSharedCheck_4359_ == 0 {
                        v_unused_4360_ = lean_ctor_get(v_x_4274_, 0);
                        lean_dec(v_unused_4360_);
                        v___x_4341_ = v_x_4274_;
                        v_isShared_4342_ = v_isSharedCheck_4359_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_v_4339_);
                        lean_dec(v_x_4274_);
                        v___x_4341_ = lean_box(0);
                        v_isShared_4342_ = v_isSharedCheck_4359_;
                        state = 8;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4291_ = lean_unsigned_to_nat(1024);
                v___x_4292_ = lean_nat_dec_le(v___x_4291_, v_prec_4275_);
                if v___x_4292_ == 0 {
                    v___x_4293_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3_once),
                        _init_l_Lake_instReprToolchainVer_repr___closed__3,
                    );
                    v___y_4281_ = v___x_4293_;
                    state = 2;
                    continue;
                } else {
                    v___x_4294_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4_once),
                        _init_l_Lake_instReprToolchainVer_repr___closed__4,
                    );
                    v___y_4281_ = v___x_4294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4282_ = l_Lake_instReprToolchainVer_repr___closed__2;
                v___x_4283_ = l_Lake_instReprStdVer_repr___redArg(v_ver_4276_);
                if v_isShared_4279_ == 0 {
                    lean_ctor_set_tag(v___x_4278_, 5);
                    lean_ctor_set(v___x_4278_, 1, v___x_4283_);
                    lean_ctor_set(v___x_4278_, 0, v___x_4282_);
                    v___x_4285_ = v___x_4278_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4290_, 0, v___x_4282_);
                    lean_ctor_set(v_reuseFailAlloc_4290_, 1, v___x_4283_);
                    v___x_4285_ = v_reuseFailAlloc_4290_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v___y_4281_);
                v___x_4286_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4286_, 0, v___y_4281_);
                lean_ctor_set(v___x_4286_, 1, v___x_4285_);
                v___x_4287_ = 0;
                v___x_4288_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4288_, 0, v___x_4286_);
                lean_ctor_set_uint8(
                    v___x_4288_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4287_,
                );
                v___x_4289_ = l_Repr_addAppParen(v___x_4288_, v_prec_4275_);
                return v___x_4289_;
            }
            4 => {
                v___x_4301_ = lean_box(1);
                v___x_4302_ = l_Lake_instReprToolchainVer_repr___closed__7;
                v___x_4303_ = lean_unsigned_to_nat(1024);
                v___x_4304_ = l_Lake_instReprDate_repr___redArg(v_date_4297_);
                v___x_4305_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4305_, 0, v___x_4302_);
                lean_ctor_set(v___x_4305_, 1, v___x_4304_);
                v___x_4306_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4306_, 0, v___x_4305_);
                lean_ctor_set(v___x_4306_, 1, v___x_4301_);
                v___x_4307_ = l_Option_repr___at___00Lake_instReprToolchainVer_repr_spec__0(
                    v_rev_4298_,
                    v___x_4303_,
                );
                v___x_4308_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4308_, 0, v___x_4306_);
                lean_ctor_set(v___x_4308_, 1, v___x_4307_);
                lean_inc(v___y_4300_);
                v___x_4309_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4309_, 0, v___y_4300_);
                lean_ctor_set(v___x_4309_, 1, v___x_4308_);
                v___x_4310_ = 0;
                v___x_4311_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4311_, 0, v___x_4309_);
                lean_ctor_set_uint8(
                    v___x_4311_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4310_,
                );
                v___x_4312_ = l_Repr_addAppParen(v___x_4311_, v_prec_4275_);
                return v___x_4312_;
            }
            5 => {
                v___x_4333_ = lean_unsigned_to_nat(1024);
                v___x_4334_ = lean_nat_dec_le(v___x_4333_, v_prec_4275_);
                if v___x_4334_ == 0 {
                    v___x_4335_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3_once),
                        _init_l_Lake_instReprToolchainVer_repr___closed__3,
                    );
                    v___y_4322_ = v___x_4335_;
                    state = 6;
                    continue;
                } else {
                    v___x_4336_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4_once),
                        _init_l_Lake_instReprToolchainVer_repr___closed__4,
                    );
                    v___y_4322_ = v___x_4336_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4323_ = l_Lake_instReprToolchainVer_repr___closed__10;
                v___x_4324_ = l_Nat_reprFast(v_n_4317_);
                v___x_4325_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4325_, 0, v___x_4324_);
                if v_isShared_4320_ == 0 {
                    lean_ctor_set_tag(v___x_4319_, 5);
                    lean_ctor_set(v___x_4319_, 1, v___x_4325_);
                    lean_ctor_set(v___x_4319_, 0, v___x_4323_);
                    v___x_4327_ = v___x_4319_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4332_, 0, v___x_4323_);
                    lean_ctor_set(v_reuseFailAlloc_4332_, 1, v___x_4325_);
                    v___x_4327_ = v_reuseFailAlloc_4332_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_inc(v___y_4322_);
                v___x_4328_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4328_, 0, v___y_4322_);
                lean_ctor_set(v___x_4328_, 1, v___x_4327_);
                v___x_4329_ = 0;
                v___x_4330_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4330_, 0, v___x_4328_);
                lean_ctor_set_uint8(
                    v___x_4330_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4329_,
                );
                v___x_4331_ = l_Repr_addAppParen(v___x_4330_, v_prec_4275_);
                return v___x_4331_;
            }
            8 => {
                v___x_4355_ = lean_unsigned_to_nat(1024);
                v___x_4356_ = lean_nat_dec_le(v___x_4355_, v_prec_4275_);
                if v___x_4356_ == 0 {
                    v___x_4357_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3_once),
                        _init_l_Lake_instReprToolchainVer_repr___closed__3,
                    );
                    v___y_4344_ = v___x_4357_;
                    state = 9;
                    continue;
                } else {
                    v___x_4358_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4_once),
                        _init_l_Lake_instReprToolchainVer_repr___closed__4,
                    );
                    v___y_4344_ = v___x_4358_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_4345_ = l_Lake_instReprToolchainVer_repr___closed__13;
                v___x_4346_ = l_String_quote(v_v_4339_);
                v___x_4347_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_4347_, 0, v___x_4346_);
                if v_isShared_4342_ == 0 {
                    lean_ctor_set_tag(v___x_4341_, 5);
                    lean_ctor_set(v___x_4341_, 1, v___x_4347_);
                    lean_ctor_set(v___x_4341_, 0, v___x_4345_);
                    v___x_4349_ = v___x_4341_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4354_, 0, v___x_4345_);
                    lean_ctor_set(v_reuseFailAlloc_4354_, 1, v___x_4347_);
                    v___x_4349_ = v_reuseFailAlloc_4354_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_inc(v___y_4344_);
                v___x_4350_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4350_, 0, v___y_4344_);
                lean_ctor_set(v___x_4350_, 1, v___x_4349_);
                v___x_4351_ = 0;
                v___x_4352_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4352_, 0, v___x_4350_);
                lean_ctor_set_uint8(
                    v___x_4352_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4351_,
                );
                v___x_4353_ = l_Repr_addAppParen(v___x_4352_, v_prec_4275_);
                return v___x_4353_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprToolchainVer_repr___boxed(
    mut v_x_4361_: *mut LeanObject,
    mut v_prec_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4363_: *mut LeanObject = core::ptr::null_mut();
    v_res_4363_ = l_Lake_instReprToolchainVer_repr(v_x_4361_, v_prec_4362_);
    lean_dec(v_prec_4362_);
    return v_res_4363_;
}
pub unsafe fn l_Lake_instDecidableEqToolchainVer_decEq(
    mut v_x_4366_: *mut LeanObject,
    mut v_x_4367_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_4366_) {
        0 => {
            if lean_obj_tag(v_x_4367_) == 0 {
                let mut v_ver_4368_: *mut LeanObject = core::ptr::null_mut();
                let mut v_ver_4369_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4370_: u8 = 0;
                v_ver_4368_ = lean_ctor_get(v_x_4366_, 1);
                lean_inc_ref(v_ver_4368_);
                lean_dec_ref_known(v_x_4366_, 2);
                v_ver_4369_ = lean_ctor_get(v_x_4367_, 1);
                lean_inc_ref(v_ver_4369_);
                lean_dec_ref_known(v_x_4367_, 2);
                v___x_4370_ = l_Lake_instDecidableEqStdVer_decEq(v_ver_4368_, v_ver_4369_);
                lean_dec_ref(v_ver_4369_);
                lean_dec_ref(v_ver_4368_);
                return v___x_4370_;
            } else {
                let mut v___x_4371_: u8 = 0;
                lean_dec_ref_known(v_x_4366_, 2);
                lean_dec_ref(v_x_4367_);
                v___x_4371_ = 0;
                return v___x_4371_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_4367_) == 1 {
                let mut v_date_4372_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rev_4373_: *mut LeanObject = core::ptr::null_mut();
                let mut v_date_4374_: *mut LeanObject = core::ptr::null_mut();
                let mut v_rev_4375_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4376_: u8 = 0;
                v_date_4372_ = lean_ctor_get(v_x_4366_, 1);
                lean_inc_ref(v_date_4372_);
                v_rev_4373_ = lean_ctor_get(v_x_4366_, 2);
                lean_inc(v_rev_4373_);
                lean_dec_ref_known(v_x_4366_, 3);
                v_date_4374_ = lean_ctor_get(v_x_4367_, 1);
                lean_inc_ref(v_date_4374_);
                v_rev_4375_ = lean_ctor_get(v_x_4367_, 2);
                lean_inc(v_rev_4375_);
                lean_dec_ref_known(v_x_4367_, 3);
                v___x_4376_ = l_Lake_instDecidableEqDate_decEq(v_date_4372_, v_date_4374_);
                lean_dec_ref(v_date_4374_);
                lean_dec_ref(v_date_4372_);
                if v___x_4376_ == 0 {
                    lean_dec(v_rev_4375_);
                    lean_dec(v_rev_4373_);
                    return v___x_4376_;
                } else {
                    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4378_: u8 = 0;
                    v___x_4377_ = lean_alloc_closure(
                        l_instDecidableEqNat___boxed as *mut core::ffi::c_void,
                        2,
                        0,
                    );
                    v___x_4378_ =
                        l_Option_instDecidableEq___redArg(v___x_4377_, v_rev_4373_, v_rev_4375_);
                    return v___x_4378_;
                }
            } else {
                let mut v___x_4379_: u8 = 0;
                lean_dec_ref_known(v_x_4366_, 3);
                lean_dec_ref(v_x_4367_);
                v___x_4379_ = 0;
                return v___x_4379_;
            }
        }
        2 => {
            if lean_obj_tag(v_x_4367_) == 2 {
                let mut v_n_4380_: *mut LeanObject = core::ptr::null_mut();
                let mut v_n_4381_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4382_: u8 = 0;
                v_n_4380_ = lean_ctor_get(v_x_4366_, 1);
                lean_inc(v_n_4380_);
                lean_dec_ref_known(v_x_4366_, 2);
                v_n_4381_ = lean_ctor_get(v_x_4367_, 1);
                lean_inc(v_n_4381_);
                lean_dec_ref_known(v_x_4367_, 2);
                v___x_4382_ = lean_nat_dec_eq(v_n_4380_, v_n_4381_);
                lean_dec(v_n_4381_);
                lean_dec(v_n_4380_);
                return v___x_4382_;
            } else {
                let mut v___x_4383_: u8 = 0;
                lean_dec_ref_known(v_x_4366_, 2);
                lean_dec_ref(v_x_4367_);
                v___x_4383_ = 0;
                return v___x_4383_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_4367_) == 3 {
                let mut v_v_4384_: *mut LeanObject = core::ptr::null_mut();
                let mut v_v_4385_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4386_: u8 = 0;
                v_v_4384_ = lean_ctor_get(v_x_4366_, 1);
                lean_inc_ref(v_v_4384_);
                lean_dec_ref_known(v_x_4366_, 2);
                v_v_4385_ = lean_ctor_get(v_x_4367_, 1);
                lean_inc_ref(v_v_4385_);
                lean_dec_ref_known(v_x_4367_, 2);
                v___x_4386_ = lean_string_dec_eq(v_v_4384_, v_v_4385_);
                lean_dec_ref(v_v_4385_);
                lean_dec_ref(v_v_4384_);
                return v___x_4386_;
            } else {
                let mut v___x_4387_: u8 = 0;
                lean_dec_ref_known(v_x_4366_, 2);
                lean_dec_ref(v_x_4367_);
                v___x_4387_ = 0;
                return v___x_4387_;
            }
        }
    }
}
pub unsafe fn l_Lake_instDecidableEqToolchainVer_decEq___boxed(
    mut v_x_4388_: *mut LeanObject,
    mut v_x_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4390_: u8 = 0;
    let mut v_r_4391_: *mut LeanObject = core::ptr::null_mut();
    v_res_4390_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_4388_, v_x_4389_);
    v_r_4391_ = lean_box((v_res_4390_) as usize);
    return v_r_4391_;
}
pub unsafe fn l_Lake_instDecidableEqToolchainVer(
    mut v_x_4392_: *mut LeanObject,
    mut v_x_4393_: *mut LeanObject,
) -> u8 {
    let mut v___x_4394_: u8 = 0;
    v___x_4394_ = l_Lake_instDecidableEqToolchainVer_decEq(v_x_4392_, v_x_4393_);
    return v___x_4394_;
}
pub unsafe fn l_Lake_instDecidableEqToolchainVer___boxed(
    mut v_x_4395_: *mut LeanObject,
    mut v_x_4396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4397_: u8 = 0;
    let mut v_r_4398_: *mut LeanObject = core::ptr::null_mut();
    v_res_4397_ = l_Lake_instDecidableEqToolchainVer(v_x_4395_, v_x_4396_);
    v_r_4398_ = lean_box((v_res_4397_) as usize);
    return v_r_4398_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    v___x_4402_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0;
    v___x_4403_ = lean_string_utf8_byte_size(v___x_4402_);
    return v___x_4403_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(
    mut v_s_4404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: u8 = 0;
    v___x_4405_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__0;
    v___x_4406_ = lean_string_utf8_byte_size(v_s_4404_);
    v___x_4407_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1_once), _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg___closed__1);
    v___x_4408_ = lean_nat_dec_le(v___x_4407_, v___x_4406_);
    if v___x_4408_ == 0 {
        let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_4404_);
        v___x_4409_ = lean_box(0);
        return v___x_4409_;
    } else {
        let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4411_: u8 = 0;
        v___x_4410_ = lean_unsigned_to_nat(0);
        v___x_4411_ = lean_string_memcmp(
            v_s_4404_,
            v___x_4405_,
            v___x_4410_,
            v___x_4410_,
            v___x_4407_,
        );
        if v___x_4411_ == 0 {
            let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_4404_);
            v___x_4412_ = lean_box(0);
            return v___x_4412_;
        } else {
            let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_s_4404_);
            v___x_4413_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4413_, 0, v_s_4404_);
            lean_ctor_set(v___x_4413_, 1, v___x_4410_);
            lean_ctor_set(v___x_4413_, 2, v___x_4406_);
            v___x_4414_ = l_String_Slice_pos_x21(v___x_4413_, v___x_4407_);
            lean_dec_ref_known(v___x_4413_, 3);
            v___x_4415_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4415_, 0, v_s_4404_);
            lean_ctor_set(v___x_4415_, 1, v___x_4414_);
            lean_ctor_set(v___x_4415_, 2, v___x_4406_);
            v___x_4416_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4416_, 0, v___x_4415_);
            return v___x_4416_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(
    mut v_s_4417_: *mut LeanObject,
    mut v_pat_4418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    v___x_4419_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(v_s_4417_);
    return v___x_4419_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___boxed(
    mut v_s_4420_: *mut LeanObject,
    mut v_pat_4421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4422_: *mut LeanObject = core::ptr::null_mut();
    v_res_4422_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0(v_s_4420_, v_pat_4421_);
    lean_dec_ref(v_pat_4421_);
    return v_res_4422_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    v___x_4423_ = l_Lake_ToolchainVer_defaultOrigin___closed__0;
    v___x_4424_ = lean_string_utf8_byte_size(v___x_4423_);
    return v___x_4424_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(
    mut v_s_4425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: u8 = 0;
    v___x_4426_ = l_Lake_ToolchainVer_defaultOrigin___closed__0;
    v___x_4427_ = lean_string_utf8_byte_size(v_s_4425_);
    v___x_4428_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0_once), _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg___closed__0);
    v___x_4429_ = lean_nat_dec_le(v___x_4428_, v___x_4427_);
    if v___x_4429_ == 0 {
        let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_4425_);
        v___x_4430_ = lean_box(0);
        return v___x_4430_;
    } else {
        let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4432_: u8 = 0;
        v___x_4431_ = lean_unsigned_to_nat(0);
        v___x_4432_ = lean_string_memcmp(
            v_s_4425_,
            v___x_4426_,
            v___x_4431_,
            v___x_4431_,
            v___x_4428_,
        );
        if v___x_4432_ == 0 {
            let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_4425_);
            v___x_4433_ = lean_box(0);
            return v___x_4433_;
        } else {
            let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4436_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_s_4425_);
            v___x_4434_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4434_, 0, v_s_4425_);
            lean_ctor_set(v___x_4434_, 1, v___x_4431_);
            lean_ctor_set(v___x_4434_, 2, v___x_4427_);
            v___x_4435_ = l_String_Slice_pos_x21(v___x_4434_, v___x_4428_);
            lean_dec_ref_known(v___x_4434_, 3);
            v___x_4436_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4436_, 0, v_s_4425_);
            lean_ctor_set(v___x_4436_, 1, v___x_4435_);
            lean_ctor_set(v___x_4436_, 2, v___x_4427_);
            v___x_4437_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4437_, 0, v___x_4436_);
            return v___x_4437_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(
    mut v_s_4438_: *mut LeanObject,
    mut v_pat_4439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    v___x_4440_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v_s_4438_);
    return v___x_4440_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___boxed(
    mut v_s_4441_: *mut LeanObject,
    mut v_pat_4442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4443_: *mut LeanObject = core::ptr::null_mut();
    v_res_4443_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1(v_s_4441_, v_pat_4442_);
    lean_dec_ref(v_pat_4442_);
    return v_res_4443_;
}
pub unsafe fn _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut LeanObject = core::ptr::null_mut();
    v___x_4445_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0;
    v___x_4446_ = lean_string_utf8_byte_size(v___x_4445_);
    return v___x_4446_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(
    mut v_s_4447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u8 = 0;
    v___x_4448_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__0;
    v___x_4449_ = lean_string_utf8_byte_size(v_s_4447_);
    v___x_4450_ = lean_obj_once(core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1_once), _init_l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg___closed__1);
    v___x_4451_ = lean_nat_dec_le(v___x_4450_, v___x_4449_);
    if v___x_4451_ == 0 {
        let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_4447_);
        v___x_4452_ = lean_box(0);
        return v___x_4452_;
    } else {
        let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4454_: u8 = 0;
        v___x_4453_ = lean_unsigned_to_nat(0);
        v___x_4454_ = lean_string_memcmp(
            v_s_4447_,
            v___x_4448_,
            v___x_4453_,
            v___x_4453_,
            v___x_4450_,
        );
        if v___x_4454_ == 0 {
            let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_s_4447_);
            v___x_4455_ = lean_box(0);
            return v___x_4455_;
        } else {
            let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4458_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_s_4447_);
            v___x_4456_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4456_, 0, v_s_4447_);
            lean_ctor_set(v___x_4456_, 1, v___x_4453_);
            lean_ctor_set(v___x_4456_, 2, v___x_4449_);
            v___x_4457_ = l_String_Slice_pos_x21(v___x_4456_, v___x_4450_);
            lean_dec_ref_known(v___x_4456_, 3);
            v___x_4458_ = lean_alloc_ctor(0, 3, (0) as u32);
            lean_ctor_set(v___x_4458_, 0, v_s_4447_);
            lean_ctor_set(v___x_4458_, 1, v___x_4457_);
            lean_ctor_set(v___x_4458_, 2, v___x_4449_);
            v___x_4459_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_4459_, 0, v___x_4458_);
            return v___x_4459_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(
    mut v_s_4460_: *mut LeanObject,
    mut v_pat_4461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    v___x_4462_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v_s_4460_);
    return v___x_4462_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___boxed(
    mut v_s_4463_: *mut LeanObject,
    mut v_pat_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_res_4465_ =
        l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3(v_s_4463_, v_pat_4464_);
    lean_dec_ref(v_pat_4464_);
    return v_res_4465_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(
    mut v___x_4466_: *mut LeanObject,
    mut v_ver_4467_: *mut LeanObject,
    mut v_a_4468_: *mut LeanObject,
    mut v_b_4469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: u8 = 0;
    let mut v___x_4474_: u32 = 0;
    let mut v___x_4475_: u32 = 0;
    let mut v___x_4476_: u8 = 0;
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_4470_ = lean_ctor_get(v___x_4466_, 1);
                v_endExclusive_4471_ = lean_ctor_get(v___x_4466_, 2);
                v___x_4472_ = lean_nat_sub(v_endExclusive_4471_, v_startInclusive_4470_);
                v___x_4473_ = lean_nat_dec_eq(v_a_4468_, v___x_4472_);
                lean_dec(v___x_4472_);
                if v___x_4473_ == 0 {
                    v___x_4474_ = lean_string_utf8_get_fast(v_ver_4467_, v_a_4468_);
                    v___x_4475_ = 58;
                    v___x_4476_ = lean_uint32_dec_eq(v___x_4474_, v___x_4475_);
                    if v___x_4476_ == 0 {
                        v___x_4477_ = lean_box(0);
                        v___x_4478_ = lean_string_utf8_next_fast(v_ver_4467_, v_a_4468_);
                        lean_dec(v_a_4468_);
                        v_a_4468_ = v___x_4478_;
                        v_b_4469_ = v___x_4477_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4480_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4480_, 0, v_a_4468_);
                        return v___x_4480_;
                    }
                } else {
                    lean_dec(v_a_4468_);
                    lean_inc(v_b_4469_);
                    return v_b_4469_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg___boxed(
    mut v___x_4481_: *mut LeanObject,
    mut v_ver_4482_: *mut LeanObject,
    mut v_a_4483_: *mut LeanObject,
    mut v_b_4484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4485_: *mut LeanObject = core::ptr::null_mut();
    v_res_4485_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(
            v___x_4481_,
            v_ver_4482_,
            v_a_4483_,
            v_b_4484_,
        );
    lean_dec(v_b_4484_);
    lean_dec_ref(v_ver_4482_);
    lean_dec_ref(v___x_4481_);
    return v_res_4485_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(
    mut v___x_4486_: *mut LeanObject,
    mut v_rest_4487_: *mut LeanObject,
    mut v_a_4488_: *mut LeanObject,
    mut v_b_4489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: u8 = 0;
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_4490_ = lean_ctor_get(v___x_4486_, 1);
                v_endExclusive_4491_ = lean_ctor_get(v___x_4486_, 2);
                v___x_4492_ = lean_nat_sub(v_endExclusive_4491_, v_startInclusive_4490_);
                v___x_4493_ = lean_nat_dec_eq(v_a_4488_, v___x_4492_);
                lean_dec(v___x_4492_);
                if v___x_4493_ == 0 {
                    v___x_4494_ = lean_string_utf8_next_fast(v_rest_4487_, v_a_4488_);
                    lean_dec(v_a_4488_);
                    v___x_4495_ = lean_unsigned_to_nat(1);
                    v___x_4496_ = lean_nat_add(v_b_4489_, v___x_4495_);
                    lean_dec(v_b_4489_);
                    v_a_4488_ = v___x_4494_;
                    v_b_4489_ = v___x_4496_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_4488_);
                    return v_b_4489_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg___boxed(
    mut v___x_4498_: *mut LeanObject,
    mut v_rest_4499_: *mut LeanObject,
    mut v_a_4500_: *mut LeanObject,
    mut v_b_4501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4502_: *mut LeanObject = core::ptr::null_mut();
    v_res_4502_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(
            v___x_4498_,
            v_rest_4499_,
            v_a_4500_,
            v_b_4501_,
        );
    lean_dec_ref(v_rest_4499_);
    lean_dec_ref(v___x_4498_);
    return v_res_4502_;
}
pub unsafe fn _init_l_Lake_ToolchainVer_ofString___closed__1() -> *mut LeanObject {
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    v___x_4504_ = l_Lake_ToolchainVer_ofString___closed__0;
    v___x_4505_ = lean_string_utf8_byte_size(v___x_4504_);
    return v___x_4505_;
}
pub unsafe fn _init_l_Lake_ToolchainVer_ofString___closed__2() -> *mut LeanObject {
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut LeanObject = core::ptr::null_mut();
    v___x_4506_ = l_Lake_ToolchainVer_nightly___override___closed__1;
    v___x_4507_ = lean_string_utf8_byte_size(v___x_4506_);
    return v___x_4507_;
}
pub unsafe fn _init_l_Lake_ToolchainVer_ofString___closed__4() -> *mut LeanObject {
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    v___x_4509_ = l_Lake_ToolchainVer_ofString___closed__3;
    v___x_4510_ = lean_string_utf8_byte_size(v___x_4509_);
    return v___x_4510_;
}
pub unsafe fn l_Lake_ToolchainVer_ofString(mut v_ver_4511_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_4513_: u8 = 0;
    let mut v___y_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4534_: u8 = 0;
    let mut v___y_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: u8 = 0;
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4547_: u8 = 0;
    let mut v___y_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4556_: u8 = 0;
    let mut v___y_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rest_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: u8 = 0;
    let mut v___x_4575_: u8 = 0;
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: u8 = 0;
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noOrigin_4610_: u8 = 0;
    let mut v___x_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: u8 = 0;
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: u8 = 0;
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: u8 = 0;
    let mut v_pos_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_4638_ = lean_unsigned_to_nat(0);
                v___x_4639_ = lean_string_utf8_byte_size(v_ver_4511_);
                lean_inc_ref(v_ver_4511_);
                v___x_4640_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4640_, 0, v_ver_4511_);
                lean_ctor_set(v___x_4640_, 1, v_searcher_4638_);
                lean_ctor_set(v___x_4640_, 2, v___x_4639_);
                v___x_4641_ = lean_box(0);
                v___x_4642_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(v___x_4640_, v_ver_4511_, v_searcher_4638_, v___x_4641_);
                lean_dec_ref_known(v___x_4640_, 3);
                if lean_obj_tag(v___x_4642_) == 0 {
                    v___y_4630_ = v___x_4639_;
                    state = 6;
                    continue;
                } else {
                    v_val_4643_ = lean_ctor_get(v___x_4642_, 0);
                    lean_inc(v_val_4643_);
                    lean_dec_ref_known(v___x_4642_, 1);
                    v___y_4630_ = v_val_4643_;
                    state = 6;
                    continue;
                }
            }
            1 => {
                if v___y_4513_ == 0 {
                    v___x_4518_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__1___redArg(v___y_4515_);
                    if lean_obj_tag(v___x_4518_) == 1 {
                        v_val_4519_ = lean_ctor_get(v___x_4518_, 0);
                        lean_inc(v_val_4519_);
                        lean_dec_ref_known(v___x_4518_, 1);
                        v_startInclusive_4520_ = lean_ctor_get(v_val_4519_, 1);
                        v_endExclusive_4521_ = lean_ctor_get(v_val_4519_, 2);
                        v___x_4522_ = lean_nat_sub(v_endExclusive_4521_, v_startInclusive_4520_);
                        v___x_4523_ = lean_nat_dec_eq(v___x_4522_, v___y_4514_);
                        lean_dec(v___x_4522_);
                        if v___x_4523_ == 0 {
                            v___x_4524_ = l_Lake_ToolchainVer_ofString___closed__0;
                            v___x_4525_ = lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lake_ToolchainVer_ofString___closed__1),
                                core::ptr::addr_of_mut!(
                                    l_Lake_ToolchainVer_ofString___closed__1_once
                                ),
                                _init_l_Lake_ToolchainVer_ofString___closed__1,
                            );
                            v___x_4526_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v___x_4526_, 0, v___x_4524_);
                            lean_ctor_set(v___x_4526_, 1, v___y_4514_);
                            lean_ctor_set(v___x_4526_, 2, v___x_4525_);
                            v___x_4527_ = l_String_Slice_beq(v_val_4519_, v___x_4526_);
                            lean_dec_ref_known(v___x_4526_, 3);
                            lean_dec(v_val_4519_);
                            if v___x_4527_ == 0 {
                                lean_dec_ref(v___y_4517_);
                                lean_dec(v___y_4516_);
                                lean_inc_ref(v_ver_4511_);
                                v___x_4528_ = lean_alloc_ctor(3, 2, (0) as u32);
                                lean_ctor_set(v___x_4528_, 0, v_ver_4511_);
                                lean_ctor_set(v___x_4528_, 1, v_ver_4511_);
                                return v___x_4528_;
                            } else {
                                lean_dec_ref(v_ver_4511_);
                                v___x_4529_ = l_Lake_ToolchainVer_nightly___override(
                                    v___y_4517_,
                                    v___y_4516_,
                                );
                                return v___x_4529_;
                            }
                        } else {
                            lean_dec(v_val_4519_);
                            lean_dec(v___y_4514_);
                            lean_dec_ref(v_ver_4511_);
                            v___x_4530_ =
                                l_Lake_ToolchainVer_nightly___override(v___y_4517_, v___y_4516_);
                            return v___x_4530_;
                        }
                    } else {
                        lean_dec(v___x_4518_);
                        lean_dec_ref(v___y_4517_);
                        lean_dec(v___y_4516_);
                        lean_dec(v___y_4514_);
                        lean_inc_ref(v_ver_4511_);
                        v___x_4531_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v___x_4531_, 0, v_ver_4511_);
                        lean_ctor_set(v___x_4531_, 1, v_ver_4511_);
                        return v___x_4531_;
                    }
                } else {
                    lean_dec_ref(v___y_4515_);
                    lean_dec(v___y_4514_);
                    lean_dec_ref(v_ver_4511_);
                    v___x_4532_ = l_Lake_ToolchainVer_nightly___override(v___y_4517_, v___y_4516_);
                    return v___x_4532_;
                }
            }
            2 => {
                v___x_4542_ = l_String_Slice_positions(v___y_4537_);
                lean_inc(v___y_4536_);
                v___x_4543_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(v___y_4537_, v___y_4540_, v___x_4542_, v___y_4536_);
                lean_dec_ref(v___y_4540_);
                lean_dec_ref(v___y_4537_);
                v___x_4544_ = lean_nat_dec_le(v___x_4543_, v___y_4538_);
                lean_dec(v___y_4538_);
                lean_dec(v___x_4543_);
                if v___x_4544_ == 0 {
                    if lean_obj_tag(v___y_4541_) == 0 {
                        if v___x_4544_ == 0 {
                            lean_dec_ref(v___y_4539_);
                            lean_dec(v___y_4536_);
                            lean_dec_ref(v___y_4535_);
                            lean_inc_ref(v_ver_4511_);
                            v___x_4545_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v___x_4545_, 0, v_ver_4511_);
                            lean_ctor_set(v___x_4545_, 1, v_ver_4511_);
                            return v___x_4545_;
                        } else {
                            v___y_4513_ = v___y_4534_;
                            v___y_4514_ = v___y_4536_;
                            v___y_4515_ = v___y_4535_;
                            v___y_4516_ = v___y_4541_;
                            v___y_4517_ = v___y_4539_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_4513_ = v___y_4534_;
                        v___y_4514_ = v___y_4536_;
                        v___y_4515_ = v___y_4535_;
                        v___y_4516_ = v___y_4541_;
                        v___y_4517_ = v___y_4539_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___y_4513_ = v___y_4534_;
                    v___y_4514_ = v___y_4536_;
                    v___y_4515_ = v___y_4535_;
                    v___y_4516_ = v___y_4541_;
                    v___y_4517_ = v___y_4539_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4554_ = lean_box(0);
                v___y_4534_ = v___y_4547_;
                v___y_4535_ = v___y_4549_;
                v___y_4536_ = v___y_4548_;
                v___y_4537_ = v___y_4550_;
                v___y_4538_ = v___y_4551_;
                v___y_4539_ = v___y_4552_;
                v___y_4540_ = v___y_4553_;
                v___y_4541_ = v___x_4554_;
                state = 2;
                continue;
            }
            4 => {
                lean_inc_ref(v___y_4559_);
                v___x_4560_ =
                    l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__0___redArg(
                        v___y_4559_,
                    );
                if lean_obj_tag(v___x_4560_) == 1 {
                    lean_dec_ref(v___y_4559_);
                    v_val_4561_ = lean_ctor_get(v___x_4560_, 0);
                    lean_inc(v_val_4561_);
                    lean_dec_ref_known(v___x_4560_, 1);
                    v_rest_4562_ = l_String_Slice_toString(v_val_4561_);
                    lean_dec(v_val_4561_);
                    v___x_4563_ = lean_unsigned_to_nat(10);
                    v___x_4564_ = lean_string_utf8_byte_size(v_rest_4562_);
                    lean_inc_n(v___y_4558_, 3);
                    lean_inc_ref_n(v_rest_4562_, 2);
                    v___x_4565_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_4565_, 0, v_rest_4562_);
                    lean_ctor_set(v___x_4565_, 1, v___y_4558_);
                    lean_ctor_set(v___x_4565_, 2, v___x_4564_);
                    v___x_4566_ = l_String_Slice_Pos_nextn(v___x_4565_, v___y_4558_, v___x_4563_);
                    lean_inc(v___x_4566_);
                    v___x_4567_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_4567_, 0, v_rest_4562_);
                    lean_ctor_set(v___x_4567_, 1, v___y_4558_);
                    lean_ctor_set(v___x_4567_, 2, v___x_4566_);
                    v___x_4568_ = l_String_Slice_toString(v___x_4567_);
                    lean_dec_ref_known(v___x_4567_, 3);
                    v___x_4569_ = l_Lake_Date_ofString_x3f(v___x_4568_);
                    if lean_obj_tag(v___x_4569_) == 1 {
                        v_val_4570_ = lean_ctor_get(v___x_4569_, 0);
                        lean_inc(v_val_4570_);
                        lean_dec_ref_known(v___x_4569_, 1);
                        v___x_4571_ = l_Lake_ToolchainVer_nightly___override___closed__1;
                        v___x_4572_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_ToolchainVer_ofString___closed__2),
                            core::ptr::addr_of_mut!(l_Lake_ToolchainVer_ofString___closed__2_once),
                            _init_l_Lake_ToolchainVer_ofString___closed__2,
                        );
                        v___x_4573_ = lean_nat_sub(v___x_4564_, v___x_4566_);
                        v___x_4574_ = lean_nat_dec_le(v___x_4572_, v___x_4573_);
                        lean_dec(v___x_4573_);
                        if v___x_4574_ == 0 {
                            lean_dec(v___x_4566_);
                            v___y_4547_ = v___y_4556_;
                            v___y_4548_ = v___y_4558_;
                            v___y_4549_ = v___y_4557_;
                            v___y_4550_ = v___x_4565_;
                            v___y_4551_ = v___x_4563_;
                            v___y_4552_ = v_val_4570_;
                            v___y_4553_ = v_rest_4562_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4575_ = lean_string_memcmp(
                                v_rest_4562_,
                                v___x_4571_,
                                v___x_4566_,
                                v___y_4558_,
                                v___x_4572_,
                            );
                            if v___x_4575_ == 0 {
                                lean_dec(v___x_4566_);
                                v___y_4547_ = v___y_4556_;
                                v___y_4548_ = v___y_4558_;
                                v___y_4549_ = v___y_4557_;
                                v___y_4550_ = v___x_4565_;
                                v___y_4551_ = v___x_4563_;
                                v___y_4552_ = v_val_4570_;
                                v___y_4553_ = v_rest_4562_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v___x_4566_);
                                lean_inc_ref_n(v_rest_4562_, 2);
                                v___x_4576_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_4576_, 0, v_rest_4562_);
                                lean_ctor_set(v___x_4576_, 1, v___x_4566_);
                                lean_ctor_set(v___x_4576_, 2, v___x_4564_);
                                v___x_4577_ = l_String_Slice_pos_x21(v___x_4576_, v___x_4572_);
                                lean_dec_ref_known(v___x_4576_, 3);
                                v___x_4578_ = lean_nat_add(v___x_4566_, v___x_4577_);
                                lean_dec(v___x_4577_);
                                lean_dec(v___x_4566_);
                                v___x_4579_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_4579_, 0, v_rest_4562_);
                                lean_ctor_set(v___x_4579_, 1, v___x_4578_);
                                lean_ctor_set(v___x_4579_, 2, v___x_4564_);
                                v___x_4580_ = l_String_Slice_toString(v___x_4579_);
                                lean_dec_ref_known(v___x_4579_, 3);
                                v___x_4581_ = lean_string_utf8_byte_size(v___x_4580_);
                                lean_inc(v___y_4558_);
                                v___x_4582_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_4582_, 0, v___x_4580_);
                                lean_ctor_set(v___x_4582_, 1, v___y_4558_);
                                lean_ctor_set(v___x_4582_, 2, v___x_4581_);
                                v___x_4583_ = l_String_Slice_toNat_x3f(v___x_4582_);
                                lean_dec_ref_known(v___x_4582_, 3);
                                v___y_4534_ = v___y_4556_;
                                v___y_4535_ = v___y_4557_;
                                v___y_4536_ = v___y_4558_;
                                v___y_4537_ = v___x_4565_;
                                v___y_4538_ = v___x_4563_;
                                v___y_4539_ = v_val_4570_;
                                v___y_4540_ = v_rest_4562_;
                                v___y_4541_ = v___x_4583_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_4569_);
                        lean_dec(v___x_4566_);
                        lean_dec_ref_known(v___x_4565_, 3);
                        lean_dec_ref(v_rest_4562_);
                        lean_dec(v___y_4558_);
                        lean_dec_ref(v___y_4557_);
                        lean_inc_ref(v_ver_4511_);
                        v___x_4584_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v___x_4584_, 0, v_ver_4511_);
                        lean_ctor_set(v___x_4584_, 1, v_ver_4511_);
                        return v___x_4584_;
                    }
                } else {
                    lean_dec(v___x_4560_);
                    lean_dec(v___y_4558_);
                    v___x_4585_ = l_String_dropPrefix_x3f___at___00Lake_ToolchainVer_ofString_spec__3___redArg(v___y_4559_);
                    if lean_obj_tag(v___x_4585_) == 1 {
                        v_val_4586_ = lean_ctor_get(v___x_4585_, 0);
                        lean_inc(v_val_4586_);
                        lean_dec_ref_known(v___x_4585_, 1);
                        v___x_4587_ = l_String_Slice_toNat_x3f(v_val_4586_);
                        lean_dec(v_val_4586_);
                        if lean_obj_tag(v___x_4587_) == 1 {
                            if v___y_4556_ == 0 {
                                v_val_4588_ = lean_ctor_get(v___x_4587_, 0);
                                lean_inc(v_val_4588_);
                                lean_dec_ref_known(v___x_4587_, 1);
                                v___x_4589_ = l_Lake_ToolchainVer_prOrigin___closed__0;
                                v___x_4590_ = lean_string_dec_eq(v___y_4557_, v___x_4589_);
                                lean_dec_ref(v___y_4557_);
                                if v___x_4590_ == 0 {
                                    lean_dec(v_val_4588_);
                                    lean_inc_ref(v_ver_4511_);
                                    v___x_4591_ = lean_alloc_ctor(3, 2, (0) as u32);
                                    lean_ctor_set(v___x_4591_, 0, v_ver_4511_);
                                    lean_ctor_set(v___x_4591_, 1, v_ver_4511_);
                                    return v___x_4591_;
                                } else {
                                    lean_dec_ref(v_ver_4511_);
                                    v___x_4592_ = l_Lake_ToolchainVer_pr___override(v_val_4588_);
                                    return v___x_4592_;
                                }
                            } else {
                                lean_dec_ref(v___y_4557_);
                                lean_dec_ref(v_ver_4511_);
                                v_val_4593_ = lean_ctor_get(v___x_4587_, 0);
                                lean_inc(v_val_4593_);
                                lean_dec_ref_known(v___x_4587_, 1);
                                v___x_4594_ = l_Lake_ToolchainVer_pr___override(v_val_4593_);
                                return v___x_4594_;
                            }
                        } else {
                            lean_dec(v___x_4587_);
                            lean_dec_ref(v___y_4557_);
                            lean_inc_ref(v_ver_4511_);
                            v___x_4595_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v___x_4595_, 0, v_ver_4511_);
                            lean_ctor_set(v___x_4595_, 1, v_ver_4511_);
                            return v___x_4595_;
                        }
                    } else {
                        lean_dec(v___x_4585_);
                        lean_inc_ref(v_ver_4511_);
                        v___x_4596_ = l_Lake_StdVer_parse(v_ver_4511_);
                        if lean_obj_tag(v___x_4596_) == 1 {
                            if v___y_4556_ == 0 {
                                v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
                                lean_inc(v_a_4597_);
                                lean_dec_ref_known(v___x_4596_, 1);
                                v___x_4598_ = l_Lake_ToolchainVer_defaultOrigin___closed__0;
                                v___x_4599_ = lean_string_dec_eq(v___y_4557_, v___x_4598_);
                                lean_dec_ref(v___y_4557_);
                                if v___x_4599_ == 0 {
                                    lean_dec(v_a_4597_);
                                    lean_inc_ref(v_ver_4511_);
                                    v___x_4600_ = lean_alloc_ctor(3, 2, (0) as u32);
                                    lean_ctor_set(v___x_4600_, 0, v_ver_4511_);
                                    lean_ctor_set(v___x_4600_, 1, v_ver_4511_);
                                    return v___x_4600_;
                                } else {
                                    lean_dec_ref(v_ver_4511_);
                                    v___x_4601_ = l_Lake_ToolchainVer_release___override(v_a_4597_);
                                    return v___x_4601_;
                                }
                            } else {
                                lean_dec_ref(v___y_4557_);
                                lean_dec_ref(v_ver_4511_);
                                v_a_4602_ = lean_ctor_get(v___x_4596_, 0);
                                lean_inc(v_a_4602_);
                                lean_dec_ref_known(v___x_4596_, 1);
                                v___x_4603_ = l_Lake_ToolchainVer_release___override(v_a_4602_);
                                return v___x_4603_;
                            }
                        } else {
                            lean_dec_ref(v___x_4596_);
                            lean_dec_ref(v___y_4557_);
                            lean_inc_ref(v_ver_4511_);
                            v___x_4604_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v___x_4604_, 0, v_ver_4511_);
                            lean_ctor_set(v___x_4604_, 1, v_ver_4511_);
                            return v___x_4604_;
                        }
                    }
                }
            }
            5 => {
                v___x_4608_ = lean_string_utf8_byte_size(v_fst_4606_);
                v___x_4609_ = lean_unsigned_to_nat(0);
                v_noOrigin_4610_ = lean_nat_dec_eq(v___x_4608_, v___x_4609_);
                v___x_4611_ = l_Lake_ToolchainVer_ofString___closed__3;
                v___x_4612_ = lean_string_utf8_byte_size(v_snd_4607_);
                v___x_4613_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_ToolchainVer_ofString___closed__4),
                    core::ptr::addr_of_mut!(l_Lake_ToolchainVer_ofString___closed__4_once),
                    _init_l_Lake_ToolchainVer_ofString___closed__4,
                );
                v___x_4614_ = lean_nat_dec_le(v___x_4613_, v___x_4612_);
                if v___x_4614_ == 0 {
                    v___y_4556_ = v_noOrigin_4610_;
                    v___y_4557_ = v_fst_4606_;
                    v___y_4558_ = v___x_4609_;
                    v___y_4559_ = v_snd_4607_;
                    state = 4;
                    continue;
                } else {
                    v___x_4615_ = lean_string_memcmp(
                        v_snd_4607_,
                        v___x_4611_,
                        v___x_4609_,
                        v___x_4609_,
                        v___x_4613_,
                    );
                    if v___x_4615_ == 0 {
                        v___y_4556_ = v_noOrigin_4610_;
                        v___y_4557_ = v_fst_4606_;
                        v___y_4558_ = v___x_4609_;
                        v___y_4559_ = v_snd_4607_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4616_ = lean_unsigned_to_nat(1);
                        lean_inc_ref(v_snd_4607_);
                        v___x_4617_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_4617_, 0, v_snd_4607_);
                        lean_ctor_set(v___x_4617_, 1, v___x_4609_);
                        lean_ctor_set(v___x_4617_, 2, v___x_4612_);
                        v___x_4618_ =
                            l_String_Slice_Pos_nextn(v___x_4617_, v___x_4609_, v___x_4616_);
                        lean_dec_ref_known(v___x_4617_, 3);
                        v___x_4619_ =
                            lean_string_utf8_extract(v_snd_4607_, v___x_4618_, v___x_4612_);
                        lean_dec(v___x_4618_);
                        lean_dec_ref(v_snd_4607_);
                        v___x_4620_ = l_Lake_StdVer_parse(v___x_4619_);
                        if lean_obj_tag(v___x_4620_) == 1 {
                            if v_noOrigin_4610_ == 0 {
                                v_a_4621_ = lean_ctor_get(v___x_4620_, 0);
                                lean_inc(v_a_4621_);
                                lean_dec_ref_known(v___x_4620_, 1);
                                v___x_4622_ = l_Lake_ToolchainVer_defaultOrigin___closed__0;
                                v___x_4623_ = lean_string_dec_eq(v_fst_4606_, v___x_4622_);
                                lean_dec_ref(v_fst_4606_);
                                if v___x_4623_ == 0 {
                                    lean_dec(v_a_4621_);
                                    lean_inc_ref(v_ver_4511_);
                                    v___x_4624_ = lean_alloc_ctor(3, 2, (0) as u32);
                                    lean_ctor_set(v___x_4624_, 0, v_ver_4511_);
                                    lean_ctor_set(v___x_4624_, 1, v_ver_4511_);
                                    return v___x_4624_;
                                } else {
                                    lean_dec_ref(v_ver_4511_);
                                    v___x_4625_ = l_Lake_ToolchainVer_release___override(v_a_4621_);
                                    return v___x_4625_;
                                }
                            } else {
                                lean_dec_ref(v_fst_4606_);
                                lean_dec_ref(v_ver_4511_);
                                v_a_4626_ = lean_ctor_get(v___x_4620_, 0);
                                lean_inc(v_a_4626_);
                                lean_dec_ref_known(v___x_4620_, 1);
                                v___x_4627_ = l_Lake_ToolchainVer_release___override(v_a_4626_);
                                return v___x_4627_;
                            }
                        } else {
                            lean_dec_ref(v___x_4620_);
                            lean_dec_ref(v_fst_4606_);
                            lean_inc_ref(v_ver_4511_);
                            v___x_4628_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v___x_4628_, 0, v_ver_4511_);
                            lean_ctor_set(v___x_4628_, 1, v_ver_4511_);
                            return v___x_4628_;
                        }
                    }
                }
            }
            6 => {
                v___x_4631_ = lean_string_utf8_byte_size(v_ver_4511_);
                v___x_4632_ = lean_nat_dec_eq(v___y_4630_, v___x_4631_);
                if v___x_4632_ == 0 {
                    v_pos_4633_ = lean_string_utf8_next_fast(v_ver_4511_, v___y_4630_);
                    v___x_4634_ = lean_unsigned_to_nat(0);
                    v___x_4635_ = lean_string_utf8_extract(v_ver_4511_, v___x_4634_, v___y_4630_);
                    lean_dec(v___y_4630_);
                    v___x_4636_ = lean_string_utf8_extract(v_ver_4511_, v_pos_4633_, v___x_4631_);
                    v_fst_4606_ = v___x_4635_;
                    v_snd_4607_ = v___x_4636_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___y_4630_);
                    v___x_4637_ =
                        l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                    lean_inc_ref(v_ver_4511_);
                    v_fst_4606_ = v___x_4637_;
                    v_snd_4607_ = v_ver_4511_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(
    mut v___x_4644_: *mut LeanObject,
    mut v_rest_4645_: *mut LeanObject,
    mut v_inst_4646_: *mut LeanObject,
    mut v_R_4647_: *mut LeanObject,
    mut v_a_4648_: *mut LeanObject,
    mut v_b_4649_: *mut LeanObject,
    mut v_c_4650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    v___x_4651_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___redArg(
            v___x_4644_,
            v_rest_4645_,
            v_a_4648_,
            v_b_4649_,
        );
    return v___x_4651_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2___boxed(
    mut v___x_4652_: *mut LeanObject,
    mut v_rest_4653_: *mut LeanObject,
    mut v_inst_4654_: *mut LeanObject,
    mut v_R_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
    mut v_b_4657_: *mut LeanObject,
    mut v_c_4658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4659_: *mut LeanObject = core::ptr::null_mut();
    v_res_4659_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__2(
        v___x_4652_,
        v_rest_4653_,
        v_inst_4654_,
        v_R_4655_,
        v_a_4656_,
        v_b_4657_,
        v_c_4658_,
    );
    lean_dec_ref(v_rest_4653_);
    lean_dec_ref(v___x_4652_);
    return v_res_4659_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(
    mut v___x_4660_: *mut LeanObject,
    mut v_ver_4661_: *mut LeanObject,
    mut v_inst_4662_: *mut LeanObject,
    mut v_R_4663_: *mut LeanObject,
    mut v_a_4664_: *mut LeanObject,
    mut v_b_4665_: *mut LeanObject,
    mut v_c_4666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    v___x_4667_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___redArg(
            v___x_4660_,
            v_ver_4661_,
            v_a_4664_,
            v_b_4665_,
        );
    return v___x_4667_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4___boxed(
    mut v___x_4668_: *mut LeanObject,
    mut v_ver_4669_: *mut LeanObject,
    mut v_inst_4670_: *mut LeanObject,
    mut v_R_4671_: *mut LeanObject,
    mut v_a_4672_: *mut LeanObject,
    mut v_b_4673_: *mut LeanObject,
    mut v_c_4674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4675_: *mut LeanObject = core::ptr::null_mut();
    v_res_4675_ = l_WellFounded_opaqueFix_u2083___at___00Lake_ToolchainVer_ofString_spec__4(
        v___x_4668_,
        v_ver_4669_,
        v_inst_4670_,
        v_R_4671_,
        v_a_4672_,
        v_b_4673_,
        v_c_4674_,
    );
    lean_dec(v_b_4673_);
    lean_dec_ref(v_ver_4669_);
    lean_dec_ref(v___x_4668_);
    return v_res_4675_;
}
pub unsafe fn l_Lake_ToolchainVer_ofFile_x3f(
    mut v_toolchainFile_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4696_: u8 = 0;
    let mut v_a_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4700_: u8 = 0;
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4678_ = l_IO_FS_readFile(v_toolchainFile_4676_);
                if lean_obj_tag(v___x_4678_) == 0 {
                    v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
                    v_isSharedCheck_4696_ = (!lean_is_exclusive(v___x_4678_)) as u8;
                    if v_isSharedCheck_4696_ == 0 {
                        v___x_4681_ = v___x_4678_;
                        v_isShared_4682_ = v_isSharedCheck_4696_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4679_);
                        lean_dec(v___x_4678_);
                        v___x_4681_ = lean_box(0);
                        v_isShared_4682_ = v_isSharedCheck_4696_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4697_ = lean_ctor_get(v___x_4678_, 0);
                    v_isSharedCheck_4708_ = (!lean_is_exclusive(v___x_4678_)) as u8;
                    if v_isSharedCheck_4708_ == 0 {
                        v___x_4699_ = v___x_4678_;
                        v_isShared_4700_ = v_isSharedCheck_4708_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4697_);
                        lean_dec(v___x_4678_);
                        v___x_4699_ = lean_box(0);
                        v_isShared_4700_ = v_isSharedCheck_4708_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4683_ = lean_unsigned_to_nat(0);
                v___x_4684_ = lean_string_utf8_byte_size(v_a_4679_);
                v___x_4685_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4685_, 0, v_a_4679_);
                lean_ctor_set(v___x_4685_, 1, v___x_4683_);
                lean_ctor_set(v___x_4685_, 2, v___x_4684_);
                v___x_4686_ = l_String_Slice_trimAscii(v___x_4685_);
                v_str_4687_ = lean_ctor_get(v___x_4686_, 0);
                lean_inc_ref(v_str_4687_);
                v_startInclusive_4688_ = lean_ctor_get(v___x_4686_, 1);
                lean_inc(v_startInclusive_4688_);
                v_endExclusive_4689_ = lean_ctor_get(v___x_4686_, 2);
                lean_inc(v_endExclusive_4689_);
                lean_dec_ref(v___x_4686_);
                v___x_4690_ = lean_string_utf8_extract(
                    v_str_4687_,
                    v_startInclusive_4688_,
                    v_endExclusive_4689_,
                );
                lean_dec(v_endExclusive_4689_);
                lean_dec(v_startInclusive_4688_);
                lean_dec_ref(v_str_4687_);
                v___x_4691_ = l_Lake_ToolchainVer_ofString(v___x_4690_);
                v___x_4692_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4692_, 0, v___x_4691_);
                if v_isShared_4682_ == 0 {
                    lean_ctor_set(v___x_4681_, 0, v___x_4692_);
                    v___x_4694_ = v___x_4681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4695_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4695_, 0, v___x_4692_);
                    v___x_4694_ = v_reuseFailAlloc_4695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4694_;
            }
            3 => {
                if lean_obj_tag(v_a_4697_) == 11 {
                    lean_dec_ref_known(v_a_4697_, 2);
                    v___x_4701_ = lean_box(0);
                    if v_isShared_4700_ == 0 {
                        lean_ctor_set_tag(v___x_4699_, 0);
                        lean_ctor_set(v___x_4699_, 0, v___x_4701_);
                        v___x_4703_ = v___x_4699_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4704_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4701_);
                        v___x_4703_ = v_reuseFailAlloc_4704_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_4700_ == 0 {
                        v___x_4706_ = v___x_4699_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4707_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4707_, 0, v_a_4697_);
                        v___x_4706_ = v_reuseFailAlloc_4707_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4703_;
            }
            5 => {
                return v___x_4706_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_ofFile_x3f___boxed(
    mut v_toolchainFile_4709_: *mut LeanObject,
    mut v_a_4710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4711_: *mut LeanObject = core::ptr::null_mut();
    v_res_4711_ = l_Lake_ToolchainVer_ofFile_x3f(v_toolchainFile_4709_);
    lean_dec_ref(v_toolchainFile_4709_);
    return v_res_4711_;
}
pub unsafe fn l_Lake_ToolchainVer_ofDir_x3f(mut v_dir_4712_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    v___x_4714_ = l_Lake_toolchainFileName___closed__0;
    v___x_4715_ = l_System_FilePath_join(v_dir_4712_, v___x_4714_);
    v___x_4716_ = l_Lake_ToolchainVer_ofFile_x3f(v___x_4715_);
    lean_dec_ref(v___x_4715_);
    return v___x_4716_;
}
pub unsafe fn l_Lake_ToolchainVer_ofDir_x3f___boxed(
    mut v_dir_4717_: *mut LeanObject,
    mut v_a_4718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4719_: *mut LeanObject = core::ptr::null_mut();
    v_res_4719_ = l_Lake_ToolchainVer_ofDir_x3f(v_dir_4717_);
    return v_res_4719_;
}
pub unsafe fn l_Lake_ToolchainVer_instToJson___lam__0(
    mut v_x_4722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toString_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    v_toString_4723_ = lean_ctor_get(v_x_4722_, 0);
    lean_inc_ref(v_toString_4723_);
    v___x_4724_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4724_, 0, v_toString_4723_);
    return v___x_4724_;
}
pub unsafe fn l_Lake_ToolchainVer_instToJson___lam__0___boxed(
    mut v_x_4725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4726_: *mut LeanObject = core::ptr::null_mut();
    v_res_4726_ = l_Lake_ToolchainVer_instToJson___lam__0(v_x_4725_);
    lean_dec_ref(v_x_4725_);
    return v_res_4726_;
}
pub unsafe fn l_Lake_ToolchainVer_instFromJson___lam__0(
    mut v_x_4729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4734_: u8 = 0;
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4738_: u8 = 0;
    let mut v_a_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v___x_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4730_ = l_Lean_Json_getStr_x3f(v_x_4729_);
                if lean_obj_tag(v___x_4730_) == 0 {
                    v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
                    v_isSharedCheck_4738_ = (!lean_is_exclusive(v___x_4730_)) as u8;
                    if v_isSharedCheck_4738_ == 0 {
                        v___x_4733_ = v___x_4730_;
                        v_isShared_4734_ = v_isSharedCheck_4738_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4731_);
                        lean_dec(v___x_4730_);
                        v___x_4733_ = lean_box(0);
                        v_isShared_4734_ = v_isSharedCheck_4738_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4739_ = lean_ctor_get(v___x_4730_, 0);
                    v_isSharedCheck_4747_ = (!lean_is_exclusive(v___x_4730_)) as u8;
                    if v_isSharedCheck_4747_ == 0 {
                        v___x_4741_ = v___x_4730_;
                        v_isShared_4742_ = v_isSharedCheck_4747_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4739_);
                        lean_dec(v___x_4730_);
                        v___x_4741_ = lean_box(0);
                        v_isShared_4742_ = v_isSharedCheck_4747_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4734_ == 0 {
                    v___x_4736_ = v___x_4733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4737_, 0, v_a_4731_);
                    v___x_4736_ = v_reuseFailAlloc_4737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4736_;
            }
            3 => {
                v___x_4743_ = l_Lake_ToolchainVer_ofString(v_a_4739_);
                if v_isShared_4742_ == 0 {
                    lean_ctor_set(v___x_4741_, 0, v___x_4743_);
                    v___x_4745_ = v___x_4741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4746_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4743_);
                    v___x_4745_ = v_reuseFailAlloc_4746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_blt(
    mut v_a_4750_: *mut LeanObject,
    mut v_b_4751_: *mut LeanObject,
) -> u8 {
    let mut v_ver_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ver_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: u8 = 0;
    let mut v___x_4755_: u8 = 0;
    let mut v___x_4756_: u8 = 0;
    let mut v___x_4757_: u8 = 0;
    let mut v_date_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_4759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: u8 = 0;
    let mut v_val_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: u8 = 0;
    let mut v___x_4768_: u8 = 0;
    let mut v___x_4769_: u8 = 0;
    let mut v___x_4770_: u8 = 0;
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_4750_) {
                0 => {
                    if lean_obj_tag(v_b_4751_) == 0 {
                        v_ver_4752_ = lean_ctor_get(v_a_4750_, 1);
                        v_ver_4753_ = lean_ctor_get(v_b_4751_, 1);
                        v___x_4754_ = l_Lake_StdVer_compare(v_ver_4752_, v_ver_4753_);
                        if v___x_4754_ == 0 {
                            v___x_4755_ = 1;
                            return v___x_4755_;
                        } else {
                            v___x_4756_ = 0;
                            return v___x_4756_;
                        }
                    } else {
                        v___x_4757_ = 0;
                        return v___x_4757_;
                    }
                }
                1 => {
                    if lean_obj_tag(v_b_4751_) == 1 {
                        v_date_4758_ = lean_ctor_get(v_a_4750_, 1);
                        v_rev_4759_ = lean_ctor_get(v_a_4750_, 2);
                        v_date_4760_ = lean_ctor_get(v_b_4751_, 1);
                        v_rev_4761_ = lean_ctor_get(v_b_4751_, 2);
                        v___x_4768_ = l_Lake_instOrdDate_ord(v_date_4758_, v_date_4760_);
                        if v___x_4768_ == 0 {
                            v___x_4769_ = 1;
                            return v___x_4769_;
                        } else {
                            v___x_4770_ =
                                l_Lake_instDecidableEqDate_decEq(v_date_4758_, v_date_4760_);
                            if v___x_4770_ == 0 {
                                return v___x_4770_;
                            } else {
                                if lean_obj_tag(v_rev_4759_) == 0 {
                                    v___x_4771_ = lean_unsigned_to_nat(0);
                                    v___y_4763_ = v___x_4771_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_4772_ = lean_ctor_get(v_rev_4759_, 0);
                                    v___y_4763_ = v_val_4772_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4773_ = 0;
                        return v___x_4773_;
                    }
                }
                _ => {
                    v___x_4774_ = 0;
                    return v___x_4774_;
                }
            },
            1 => {
                if lean_obj_tag(v_rev_4761_) == 0 {
                    v___x_4764_ = lean_unsigned_to_nat(0);
                    v___x_4765_ = lean_nat_dec_lt(v___y_4763_, v___x_4764_);
                    return v___x_4765_;
                } else {
                    v_val_4766_ = lean_ctor_get(v_rev_4761_, 0);
                    v___x_4767_ = lean_nat_dec_lt(v___y_4763_, v_val_4766_);
                    return v___x_4767_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_blt___boxed(
    mut v_a_4775_: *mut LeanObject,
    mut v_b_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4777_: u8 = 0;
    let mut v_r_4778_: *mut LeanObject = core::ptr::null_mut();
    v_res_4777_ = l_Lake_ToolchainVer_blt(v_a_4775_, v_b_4776_);
    lean_dec_ref(v_b_4776_);
    lean_dec_ref(v_a_4775_);
    v_r_4778_ = lean_box((v_res_4777_) as usize);
    return v_r_4778_;
}
pub unsafe fn _init_l_Lake_ToolchainVer_instLT() -> *mut LeanObject {
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    v___x_4779_ = lean_box(0);
    return v___x_4779_;
}
pub unsafe fn l_Lake_ToolchainVer_decLt(
    mut v_a_4780_: *mut LeanObject,
    mut v_b_4781_: *mut LeanObject,
) -> u8 {
    let mut v___x_4782_: u8 = 0;
    v___x_4782_ = l_Lake_ToolchainVer_blt(v_a_4780_, v_b_4781_);
    return v___x_4782_;
}
pub unsafe fn l_Lake_ToolchainVer_decLt___boxed(
    mut v_a_4783_: *mut LeanObject,
    mut v_b_4784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4785_: u8 = 0;
    let mut v_r_4786_: *mut LeanObject = core::ptr::null_mut();
    v_res_4785_ = l_Lake_ToolchainVer_decLt(v_a_4783_, v_b_4784_);
    lean_dec_ref(v_b_4784_);
    lean_dec_ref(v_a_4783_);
    v_r_4786_ = lean_box((v_res_4785_) as usize);
    return v_r_4786_;
}
pub unsafe fn l_Lake_ToolchainVer_ble(
    mut v_a_4787_: *mut LeanObject,
    mut v_b_4788_: *mut LeanObject,
) -> u8 {
    let mut v_ver_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ver_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: u8 = 0;
    let mut v___x_4793_: u8 = 0;
    let mut v___x_4794_: u8 = 0;
    let mut v_date_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rev_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: u8 = 0;
    let mut v_val_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: u8 = 0;
    let mut v___x_4805_: u8 = 0;
    let mut v___x_4806_: u8 = 0;
    let mut v___x_4807_: u8 = 0;
    let mut v___x_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut v_n_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: u8 = 0;
    let mut v___x_4814_: u8 = 0;
    let mut v_v_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: u8 = 0;
    let mut v___x_4818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_a_4787_) {
                0 => {
                    if lean_obj_tag(v_b_4788_) == 0 {
                        v_ver_4789_ = lean_ctor_get(v_a_4787_, 1);
                        v_ver_4790_ = lean_ctor_get(v_b_4788_, 1);
                        v___x_4791_ = l_Lake_StdVer_compare(v_ver_4789_, v_ver_4790_);
                        if v___x_4791_ == 2 {
                            v___x_4792_ = 0;
                            return v___x_4792_;
                        } else {
                            v___x_4793_ = 1;
                            return v___x_4793_;
                        }
                    } else {
                        v___x_4794_ = 0;
                        return v___x_4794_;
                    }
                }
                1 => {
                    if lean_obj_tag(v_b_4788_) == 1 {
                        v_date_4795_ = lean_ctor_get(v_a_4787_, 1);
                        v_rev_4796_ = lean_ctor_get(v_a_4787_, 2);
                        v_date_4797_ = lean_ctor_get(v_b_4788_, 1);
                        v_rev_4798_ = lean_ctor_get(v_b_4788_, 2);
                        v___x_4805_ = l_Lake_instOrdDate_ord(v_date_4795_, v_date_4797_);
                        if v___x_4805_ == 0 {
                            v___x_4806_ = 1;
                            return v___x_4806_;
                        } else {
                            v___x_4807_ =
                                l_Lake_instDecidableEqDate_decEq(v_date_4795_, v_date_4797_);
                            if v___x_4807_ == 0 {
                                return v___x_4807_;
                            } else {
                                if lean_obj_tag(v_rev_4796_) == 0 {
                                    v___x_4808_ = lean_unsigned_to_nat(0);
                                    v___y_4800_ = v___x_4808_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_4809_ = lean_ctor_get(v_rev_4796_, 0);
                                    v___y_4800_ = v_val_4809_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_4810_ = 0;
                        return v___x_4810_;
                    }
                }
                2 => {
                    if lean_obj_tag(v_b_4788_) == 2 {
                        v_n_4811_ = lean_ctor_get(v_a_4787_, 1);
                        v_n_4812_ = lean_ctor_get(v_b_4788_, 1);
                        v___x_4813_ = lean_nat_dec_eq(v_n_4811_, v_n_4812_);
                        return v___x_4813_;
                    } else {
                        v___x_4814_ = 0;
                        return v___x_4814_;
                    }
                }
                _ => {
                    if lean_obj_tag(v_b_4788_) == 3 {
                        v_v_4815_ = lean_ctor_get(v_a_4787_, 1);
                        v_v_4816_ = lean_ctor_get(v_b_4788_, 1);
                        v___x_4817_ = lean_string_dec_eq(v_v_4815_, v_v_4816_);
                        return v___x_4817_;
                    } else {
                        v___x_4818_ = 0;
                        return v___x_4818_;
                    }
                }
            },
            1 => {
                if lean_obj_tag(v_rev_4798_) == 0 {
                    v___x_4801_ = lean_unsigned_to_nat(0);
                    v___x_4802_ = lean_nat_dec_le(v___y_4800_, v___x_4801_);
                    return v___x_4802_;
                } else {
                    v_val_4803_ = lean_ctor_get(v_rev_4798_, 0);
                    v___x_4804_ = lean_nat_dec_le(v___y_4800_, v_val_4803_);
                    return v___x_4804_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ToolchainVer_ble___boxed(
    mut v_a_4819_: *mut LeanObject,
    mut v_b_4820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4821_: u8 = 0;
    let mut v_r_4822_: *mut LeanObject = core::ptr::null_mut();
    v_res_4821_ = l_Lake_ToolchainVer_ble(v_a_4819_, v_b_4820_);
    lean_dec_ref(v_b_4820_);
    lean_dec_ref(v_a_4819_);
    v_r_4822_ = lean_box((v_res_4821_) as usize);
    return v_r_4822_;
}
pub unsafe fn _init_l_Lake_ToolchainVer_instLE() -> *mut LeanObject {
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    v___x_4823_ = lean_box(0);
    return v___x_4823_;
}
pub unsafe fn l_Lake_ToolchainVer_decLe(
    mut v_a_4824_: *mut LeanObject,
    mut v_b_4825_: *mut LeanObject,
) -> u8 {
    let mut v___x_4826_: u8 = 0;
    v___x_4826_ = l_Lake_ToolchainVer_ble(v_a_4824_, v_b_4825_);
    return v___x_4826_;
}
pub unsafe fn l_Lake_ToolchainVer_decLe___boxed(
    mut v_a_4827_: *mut LeanObject,
    mut v_b_4828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4829_: u8 = 0;
    let mut v_r_4830_: *mut LeanObject = core::ptr::null_mut();
    v_res_4829_ = l_Lake_ToolchainVer_decLe(v_a_4827_, v_b_4828_);
    lean_dec_ref(v_b_4828_);
    lean_dec_ref(v_a_4827_);
    v_r_4830_ = lean_box((v_res_4829_) as usize);
    return v_r_4830_;
}
pub unsafe fn l_Lake_normalizeToolchain(mut v_s_4831_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toString_4833_: *mut LeanObject = core::ptr::null_mut();
    v___x_4832_ = l_Lake_ToolchainVer_ofString(v_s_4831_);
    v_toString_4833_ = lean_ctor_get(v___x_4832_, 0);
    lean_inc_ref(v_toString_4833_);
    lean_dec_ref(v___x_4832_);
    return v_toString_4833_;
}
pub unsafe fn l_Lake_instDecodeVersionToolchainVer___lam__0(
    mut v_x_4838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    v___x_4839_ = l_Lake_ToolchainVer_ofString(v_x_4838_);
    v___x_4840_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4840_, 0, v___x_4839_);
    return v___x_4840_;
}
pub unsafe fn l_Lake_ComparatorOp_ctorIdx(mut v_x_4843_: u8) -> *mut LeanObject {
    match v_x_4843_ {
        0 => {
            let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
            v___x_4844_ = lean_unsigned_to_nat(0);
            return v___x_4844_;
        }
        1 => {
            let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
            v___x_4845_ = lean_unsigned_to_nat(1);
            return v___x_4845_;
        }
        2 => {
            let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
            v___x_4846_ = lean_unsigned_to_nat(2);
            return v___x_4846_;
        }
        3 => {
            let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
            v___x_4847_ = lean_unsigned_to_nat(3);
            return v___x_4847_;
        }
        4 => {
            let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
            v___x_4848_ = lean_unsigned_to_nat(4);
            return v___x_4848_;
        }
        _ => {
            let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
            v___x_4849_ = lean_unsigned_to_nat(5);
            return v___x_4849_;
        }
    }
}
pub unsafe fn l_Lake_ComparatorOp_ctorIdx___boxed(
    mut v_x_4850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_4851_: u8 = 0;
    let mut v_res_4852_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_4851_ = (lean_unbox(v_x_4850_) as u8);
    v_res_4852_ = l_Lake_ComparatorOp_ctorIdx(v_x_boxed_4851_);
    return v_res_4852_;
}
pub unsafe fn l_Lake_ComparatorOp_toCtorIdx(mut v_x_4853_: u8) -> *mut LeanObject {
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    v___x_4854_ = l_Lake_ComparatorOp_ctorIdx(v_x_4853_);
    return v___x_4854_;
}
pub unsafe fn l_Lake_ComparatorOp_toCtorIdx___boxed(
    mut v_x_4855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_4856_: u8 = 0;
    let mut v_res_4857_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4856_ = (lean_unbox(v_x_4855_) as u8);
    v_res_4857_ = l_Lake_ComparatorOp_toCtorIdx(v_x_4__boxed_4856_);
    return v_res_4857_;
}
pub unsafe fn l_Lake_ComparatorOp_ctorElim___redArg(
    mut v_k_4858_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4858_);
    return v_k_4858_;
}
pub unsafe fn l_Lake_ComparatorOp_ctorElim___redArg___boxed(
    mut v_k_4859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4860_: *mut LeanObject = core::ptr::null_mut();
    v_res_4860_ = l_Lake_ComparatorOp_ctorElim___redArg(v_k_4859_);
    lean_dec(v_k_4859_);
    return v_res_4860_;
}
pub unsafe fn l_Lake_ComparatorOp_ctorElim(
    mut v_motive_4861_: *mut LeanObject,
    mut v_ctorIdx_4862_: *mut LeanObject,
    mut v_t_4863_: u8,
    mut v_h_4864_: *mut LeanObject,
    mut v_k_4865_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_4865_);
    return v_k_4865_;
}
pub unsafe fn l_Lake_ComparatorOp_ctorElim___boxed(
    mut v_motive_4866_: *mut LeanObject,
    mut v_ctorIdx_4867_: *mut LeanObject,
    mut v_t_4868_: *mut LeanObject,
    mut v_h_4869_: *mut LeanObject,
    mut v_k_4870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4871_: u8 = 0;
    let mut v_res_4872_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4871_ = (lean_unbox(v_t_4868_) as u8);
    v_res_4872_ = l_Lake_ComparatorOp_ctorElim(
        v_motive_4866_,
        v_ctorIdx_4867_,
        v_t_boxed_4871_,
        v_h_4869_,
        v_k_4870_,
    );
    lean_dec(v_k_4870_);
    lean_dec(v_ctorIdx_4867_);
    return v_res_4872_;
}
pub unsafe fn l_Lake_ComparatorOp_lt_elim___redArg(
    mut v_lt_4873_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_lt_4873_);
    return v_lt_4873_;
}
pub unsafe fn l_Lake_ComparatorOp_lt_elim___redArg___boxed(
    mut v_lt_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4875_: *mut LeanObject = core::ptr::null_mut();
    v_res_4875_ = l_Lake_ComparatorOp_lt_elim___redArg(v_lt_4874_);
    lean_dec(v_lt_4874_);
    return v_res_4875_;
}
pub unsafe fn l_Lake_ComparatorOp_lt_elim(
    mut v_motive_4876_: *mut LeanObject,
    mut v_t_4877_: u8,
    mut v_h_4878_: *mut LeanObject,
    mut v_lt_4879_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_lt_4879_);
    return v_lt_4879_;
}
pub unsafe fn l_Lake_ComparatorOp_lt_elim___boxed(
    mut v_motive_4880_: *mut LeanObject,
    mut v_t_4881_: *mut LeanObject,
    mut v_h_4882_: *mut LeanObject,
    mut v_lt_4883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4884_: u8 = 0;
    let mut v_res_4885_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4884_ = (lean_unbox(v_t_4881_) as u8);
    v_res_4885_ =
        l_Lake_ComparatorOp_lt_elim(v_motive_4880_, v_t_boxed_4884_, v_h_4882_, v_lt_4883_);
    lean_dec(v_lt_4883_);
    return v_res_4885_;
}
pub unsafe fn l_Lake_ComparatorOp_le_elim___redArg(
    mut v_le_4886_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_le_4886_);
    return v_le_4886_;
}
pub unsafe fn l_Lake_ComparatorOp_le_elim___redArg___boxed(
    mut v_le_4887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4888_: *mut LeanObject = core::ptr::null_mut();
    v_res_4888_ = l_Lake_ComparatorOp_le_elim___redArg(v_le_4887_);
    lean_dec(v_le_4887_);
    return v_res_4888_;
}
pub unsafe fn l_Lake_ComparatorOp_le_elim(
    mut v_motive_4889_: *mut LeanObject,
    mut v_t_4890_: u8,
    mut v_h_4891_: *mut LeanObject,
    mut v_le_4892_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_le_4892_);
    return v_le_4892_;
}
pub unsafe fn l_Lake_ComparatorOp_le_elim___boxed(
    mut v_motive_4893_: *mut LeanObject,
    mut v_t_4894_: *mut LeanObject,
    mut v_h_4895_: *mut LeanObject,
    mut v_le_4896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4897_: u8 = 0;
    let mut v_res_4898_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4897_ = (lean_unbox(v_t_4894_) as u8);
    v_res_4898_ =
        l_Lake_ComparatorOp_le_elim(v_motive_4893_, v_t_boxed_4897_, v_h_4895_, v_le_4896_);
    lean_dec(v_le_4896_);
    return v_res_4898_;
}
pub unsafe fn l_Lake_ComparatorOp_gt_elim___redArg(
    mut v_gt_4899_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_gt_4899_);
    return v_gt_4899_;
}
pub unsafe fn l_Lake_ComparatorOp_gt_elim___redArg___boxed(
    mut v_gt_4900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4901_: *mut LeanObject = core::ptr::null_mut();
    v_res_4901_ = l_Lake_ComparatorOp_gt_elim___redArg(v_gt_4900_);
    lean_dec(v_gt_4900_);
    return v_res_4901_;
}
pub unsafe fn l_Lake_ComparatorOp_gt_elim(
    mut v_motive_4902_: *mut LeanObject,
    mut v_t_4903_: u8,
    mut v_h_4904_: *mut LeanObject,
    mut v_gt_4905_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_gt_4905_);
    return v_gt_4905_;
}
pub unsafe fn l_Lake_ComparatorOp_gt_elim___boxed(
    mut v_motive_4906_: *mut LeanObject,
    mut v_t_4907_: *mut LeanObject,
    mut v_h_4908_: *mut LeanObject,
    mut v_gt_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4910_: u8 = 0;
    let mut v_res_4911_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4910_ = (lean_unbox(v_t_4907_) as u8);
    v_res_4911_ =
        l_Lake_ComparatorOp_gt_elim(v_motive_4906_, v_t_boxed_4910_, v_h_4908_, v_gt_4909_);
    lean_dec(v_gt_4909_);
    return v_res_4911_;
}
pub unsafe fn l_Lake_ComparatorOp_ge_elim___redArg(
    mut v_ge_4912_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ge_4912_);
    return v_ge_4912_;
}
pub unsafe fn l_Lake_ComparatorOp_ge_elim___redArg___boxed(
    mut v_ge_4913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4914_: *mut LeanObject = core::ptr::null_mut();
    v_res_4914_ = l_Lake_ComparatorOp_ge_elim___redArg(v_ge_4913_);
    lean_dec(v_ge_4913_);
    return v_res_4914_;
}
pub unsafe fn l_Lake_ComparatorOp_ge_elim(
    mut v_motive_4915_: *mut LeanObject,
    mut v_t_4916_: u8,
    mut v_h_4917_: *mut LeanObject,
    mut v_ge_4918_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ge_4918_);
    return v_ge_4918_;
}
pub unsafe fn l_Lake_ComparatorOp_ge_elim___boxed(
    mut v_motive_4919_: *mut LeanObject,
    mut v_t_4920_: *mut LeanObject,
    mut v_h_4921_: *mut LeanObject,
    mut v_ge_4922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4923_: u8 = 0;
    let mut v_res_4924_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4923_ = (lean_unbox(v_t_4920_) as u8);
    v_res_4924_ =
        l_Lake_ComparatorOp_ge_elim(v_motive_4919_, v_t_boxed_4923_, v_h_4921_, v_ge_4922_);
    lean_dec(v_ge_4922_);
    return v_res_4924_;
}
pub unsafe fn l_Lake_ComparatorOp_eq_elim___redArg(
    mut v_eq_4925_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eq_4925_);
    return v_eq_4925_;
}
pub unsafe fn l_Lake_ComparatorOp_eq_elim___redArg___boxed(
    mut v_eq_4926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4927_: *mut LeanObject = core::ptr::null_mut();
    v_res_4927_ = l_Lake_ComparatorOp_eq_elim___redArg(v_eq_4926_);
    lean_dec(v_eq_4926_);
    return v_res_4927_;
}
pub unsafe fn l_Lake_ComparatorOp_eq_elim(
    mut v_motive_4928_: *mut LeanObject,
    mut v_t_4929_: u8,
    mut v_h_4930_: *mut LeanObject,
    mut v_eq_4931_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_eq_4931_);
    return v_eq_4931_;
}
pub unsafe fn l_Lake_ComparatorOp_eq_elim___boxed(
    mut v_motive_4932_: *mut LeanObject,
    mut v_t_4933_: *mut LeanObject,
    mut v_h_4934_: *mut LeanObject,
    mut v_eq_4935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4936_: u8 = 0;
    let mut v_res_4937_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4936_ = (lean_unbox(v_t_4933_) as u8);
    v_res_4937_ =
        l_Lake_ComparatorOp_eq_elim(v_motive_4932_, v_t_boxed_4936_, v_h_4934_, v_eq_4935_);
    lean_dec(v_eq_4935_);
    return v_res_4937_;
}
pub unsafe fn l_Lake_ComparatorOp_ne_elim___redArg(
    mut v_ne_4938_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ne_4938_);
    return v_ne_4938_;
}
pub unsafe fn l_Lake_ComparatorOp_ne_elim___redArg___boxed(
    mut v_ne_4939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4940_: *mut LeanObject = core::ptr::null_mut();
    v_res_4940_ = l_Lake_ComparatorOp_ne_elim___redArg(v_ne_4939_);
    lean_dec(v_ne_4939_);
    return v_res_4940_;
}
pub unsafe fn l_Lake_ComparatorOp_ne_elim(
    mut v_motive_4941_: *mut LeanObject,
    mut v_t_4942_: u8,
    mut v_h_4943_: *mut LeanObject,
    mut v_ne_4944_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_ne_4944_);
    return v_ne_4944_;
}
pub unsafe fn l_Lake_ComparatorOp_ne_elim___boxed(
    mut v_motive_4945_: *mut LeanObject,
    mut v_t_4946_: *mut LeanObject,
    mut v_h_4947_: *mut LeanObject,
    mut v_ne_4948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_4949_: u8 = 0;
    let mut v_res_4950_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_4949_ = (lean_unbox(v_t_4946_) as u8);
    v_res_4950_ =
        l_Lake_ComparatorOp_ne_elim(v_motive_4945_, v_t_boxed_4949_, v_h_4947_, v_ne_4948_);
    lean_dec(v_ne_4948_);
    return v_res_4950_;
}
pub unsafe fn l_Lake_instReprComparatorOp_repr(
    mut v_x_4969_: u8,
    mut v_prec_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: u8 = 0;
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: u8 = 0;
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: u8 = 0;
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: u8 = 0;
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: u8 = 0;
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: u8 = 0;
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: u8 = 0;
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: u8 = 0;
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: u8 = 0;
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: u8 = 0;
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: u8 = 0;
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4969_ {
                0 => {
                    v___x_5013_ = lean_unsigned_to_nat(1024);
                    v___x_5014_ = lean_nat_dec_le(v___x_5013_, v_prec_4970_);
                    if v___x_5014_ == 0 {
                        v___x_5015_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__3,
                        );
                        v___y_4972_ = v___x_5015_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5016_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__4,
                        );
                        v___y_4972_ = v___x_5016_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_5017_ = lean_unsigned_to_nat(1024);
                    v___x_5018_ = lean_nat_dec_le(v___x_5017_, v_prec_4970_);
                    if v___x_5018_ == 0 {
                        v___x_5019_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__3,
                        );
                        v___y_4979_ = v___x_5019_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5020_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__4,
                        );
                        v___y_4979_ = v___x_5020_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_5021_ = lean_unsigned_to_nat(1024);
                    v___x_5022_ = lean_nat_dec_le(v___x_5021_, v_prec_4970_);
                    if v___x_5022_ == 0 {
                        v___x_5023_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__3,
                        );
                        v___y_4986_ = v___x_5023_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5024_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__4,
                        );
                        v___y_4986_ = v___x_5024_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v___x_5025_ = lean_unsigned_to_nat(1024);
                    v___x_5026_ = lean_nat_dec_le(v___x_5025_, v_prec_4970_);
                    if v___x_5026_ == 0 {
                        v___x_5027_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__3,
                        );
                        v___y_4993_ = v___x_5027_;
                        state = 4;
                        continue;
                    } else {
                        v___x_5028_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__4,
                        );
                        v___y_4993_ = v___x_5028_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v___x_5029_ = lean_unsigned_to_nat(1024);
                    v___x_5030_ = lean_nat_dec_le(v___x_5029_, v_prec_4970_);
                    if v___x_5030_ == 0 {
                        v___x_5031_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__3,
                        );
                        v___y_5000_ = v___x_5031_;
                        state = 5;
                        continue;
                    } else {
                        v___x_5032_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__4,
                        );
                        v___y_5000_ = v___x_5032_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v___x_5033_ = lean_unsigned_to_nat(1024);
                    v___x_5034_ = lean_nat_dec_le(v___x_5033_, v_prec_4970_);
                    if v___x_5034_ == 0 {
                        v___x_5035_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__3_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__3,
                        );
                        v___y_5007_ = v___x_5035_;
                        state = 6;
                        continue;
                    } else {
                        v___x_5036_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprToolchainVer_repr___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lake_instReprToolchainVer_repr___closed__4_once
                            ),
                            _init_l_Lake_instReprToolchainVer_repr___closed__4,
                        );
                        v___y_5007_ = v___x_5036_;
                        state = 6;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4973_ = l_Lake_instReprComparatorOp_repr___closed__1;
                lean_inc(v___y_4972_);
                v___x_4974_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4974_, 0, v___y_4972_);
                lean_ctor_set(v___x_4974_, 1, v___x_4973_);
                v___x_4975_ = 0;
                v___x_4976_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4976_, 0, v___x_4974_);
                lean_ctor_set_uint8(
                    v___x_4976_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4975_,
                );
                v___x_4977_ = l_Repr_addAppParen(v___x_4976_, v_prec_4970_);
                return v___x_4977_;
            }
            2 => {
                v___x_4980_ = l_Lake_instReprComparatorOp_repr___closed__3;
                lean_inc(v___y_4979_);
                v___x_4981_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4981_, 0, v___y_4979_);
                lean_ctor_set(v___x_4981_, 1, v___x_4980_);
                v___x_4982_ = 0;
                v___x_4983_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4983_, 0, v___x_4981_);
                lean_ctor_set_uint8(
                    v___x_4983_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4982_,
                );
                v___x_4984_ = l_Repr_addAppParen(v___x_4983_, v_prec_4970_);
                return v___x_4984_;
            }
            3 => {
                v___x_4987_ = l_Lake_instReprComparatorOp_repr___closed__5;
                lean_inc(v___y_4986_);
                v___x_4988_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4988_, 0, v___y_4986_);
                lean_ctor_set(v___x_4988_, 1, v___x_4987_);
                v___x_4989_ = 0;
                v___x_4990_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4990_, 0, v___x_4988_);
                lean_ctor_set_uint8(
                    v___x_4990_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4989_,
                );
                v___x_4991_ = l_Repr_addAppParen(v___x_4990_, v_prec_4970_);
                return v___x_4991_;
            }
            4 => {
                v___x_4994_ = l_Lake_instReprComparatorOp_repr___closed__7;
                lean_inc(v___y_4993_);
                v___x_4995_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4995_, 0, v___y_4993_);
                lean_ctor_set(v___x_4995_, 1, v___x_4994_);
                v___x_4996_ = 0;
                v___x_4997_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_4997_, 0, v___x_4995_);
                lean_ctor_set_uint8(
                    v___x_4997_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4996_,
                );
                v___x_4998_ = l_Repr_addAppParen(v___x_4997_, v_prec_4970_);
                return v___x_4998_;
            }
            5 => {
                v___x_5001_ = l_Lake_instReprComparatorOp_repr___closed__9;
                lean_inc(v___y_5000_);
                v___x_5002_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5002_, 0, v___y_5000_);
                lean_ctor_set(v___x_5002_, 1, v___x_5001_);
                v___x_5003_ = 0;
                v___x_5004_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5004_, 0, v___x_5002_);
                lean_ctor_set_uint8(
                    v___x_5004_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5003_,
                );
                v___x_5005_ = l_Repr_addAppParen(v___x_5004_, v_prec_4970_);
                return v___x_5005_;
            }
            6 => {
                v___x_5008_ = l_Lake_instReprComparatorOp_repr___closed__11;
                lean_inc(v___y_5007_);
                v___x_5009_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5009_, 0, v___y_5007_);
                lean_ctor_set(v___x_5009_, 1, v___x_5008_);
                v___x_5010_ = 0;
                v___x_5011_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5011_, 0, v___x_5009_);
                lean_ctor_set_uint8(
                    v___x_5011_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5010_,
                );
                v___x_5012_ = l_Repr_addAppParen(v___x_5011_, v_prec_4970_);
                return v___x_5012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprComparatorOp_repr___boxed(
    mut v_x_5037_: *mut LeanObject,
    mut v_prec_5038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_341__boxed_5039_: u8 = 0;
    let mut v_res_5040_: *mut LeanObject = core::ptr::null_mut();
    v_x_341__boxed_5039_ = (lean_unbox(v_x_5037_) as u8);
    v_res_5040_ = l_Lake_instReprComparatorOp_repr(v_x_341__boxed_5039_, v_prec_5038_);
    lean_dec(v_prec_5038_);
    return v_res_5040_;
}
pub unsafe fn _init_l_Lake_instInhabitedComparatorOp_default() -> u8 {
    let mut v___x_5043_: u8 = 0;
    v___x_5043_ = 0;
    return v___x_5043_;
}
pub unsafe fn _init_l_Lake_instInhabitedComparatorOp() -> u8 {
    let mut v___x_5044_: u8 = 0;
    v___x_5044_ = 0;
    return v___x_5044_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
    mut v_sym_5045_: *mut LeanObject,
    mut v_cmp_5046_: u8,
    mut v_t_5047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    v___x_5048_ = lean_box((v_cmp_5046_) as usize);
    lean_inc_ref(v_sym_5045_);
    v___x_5049_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5049_, 0, v_sym_5045_);
    lean_ctor_set(v___x_5049_, 1, v___x_5048_);
    v___x_5050_ = l_Lean_Data_Trie_insert___redArg(v_t_5047_, v_sym_5045_, v___x_5049_);
    lean_dec_ref(v_sym_5045_);
    return v___x_5050_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0___boxed(
    mut v_sym_5051_: *mut LeanObject,
    mut v_cmp_5052_: *mut LeanObject,
    mut v_t_5053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cmp_boxed_5054_: u8 = 0;
    let mut v_res_5055_: *mut LeanObject = core::ptr::null_mut();
    v_cmp_boxed_5054_ = (lean_unbox(v_cmp_5052_) as u8);
    v_res_5055_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v_sym_5051_,
        v_cmp_boxed_5054_,
        v_t_5053_,
    );
    return v_res_5055_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9()
-> *mut LeanObject {
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    v___x_5065_ = l_Lean_Data_Trie_empty(lean_box(0));
    return v___x_5065_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10()
-> *mut LeanObject {
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: u8 = 0;
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    v___x_5066_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__9,
    );
    v___x_5067_ = 0;
    v___x_5068_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8;
    v___x_5069_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5068_,
        v___x_5067_,
        v___x_5066_,
    );
    return v___x_5069_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11()
-> *mut LeanObject {
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: u8 = 0;
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    v___x_5070_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__10,
    );
    v___x_5071_ = 1;
    v___x_5072_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__7;
    v___x_5073_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5072_,
        v___x_5071_,
        v___x_5070_,
    );
    return v___x_5073_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12()
-> *mut LeanObject {
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: u8 = 0;
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    v___x_5074_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__11,
    );
    v___x_5075_ = 1;
    v___x_5076_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6;
    v___x_5077_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5076_,
        v___x_5075_,
        v___x_5074_,
    );
    return v___x_5077_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13()
-> *mut LeanObject {
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: u8 = 0;
    let mut v___x_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    v___x_5078_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__12,
    );
    v___x_5079_ = 2;
    v___x_5080_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5;
    v___x_5081_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5080_,
        v___x_5079_,
        v___x_5078_,
    );
    return v___x_5081_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14()
-> *mut LeanObject {
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut LeanObject = core::ptr::null_mut();
    v___x_5082_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__13,
    );
    v___x_5083_ = 3;
    v___x_5084_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__4;
    v___x_5085_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5084_,
        v___x_5083_,
        v___x_5082_,
    );
    return v___x_5085_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15()
-> *mut LeanObject {
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: u8 = 0;
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    v___x_5086_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__14,
    );
    v___x_5087_ = 3;
    v___x_5088_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3;
    v___x_5089_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5088_,
        v___x_5087_,
        v___x_5086_,
    );
    return v___x_5089_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16()
-> *mut LeanObject {
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: u8 = 0;
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    v___x_5090_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__15,
    );
    v___x_5091_ = 4;
    v___x_5092_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2;
    v___x_5093_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5092_,
        v___x_5091_,
        v___x_5090_,
    );
    return v___x_5093_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17()
-> *mut LeanObject {
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: u8 = 0;
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    v___x_5094_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__16,
    );
    v___x_5095_ = 5;
    v___x_5096_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__1;
    v___x_5097_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5096_,
        v___x_5095_,
        v___x_5094_,
    );
    return v___x_5097_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18()
-> *mut LeanObject {
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: u8 = 0;
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    v___x_5098_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__17,
    );
    v___x_5099_ = 5;
    v___x_5100_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0;
    v___x_5101_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___lam__0(
        v___x_5100_,
        v___x_5099_,
        v___x_5098_,
    );
    return v___x_5101_;
}
pub unsafe fn _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie()
-> *mut LeanObject {
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    v___x_5102_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18
        ),
        core::ptr::addr_of_mut!(
            l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18_once
        ),
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__18,
    );
    return v___x_5102_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(
    mut v_s_5105_: *mut LeanObject,
    mut v_p_5106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_x27_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: u8 = 0;
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5126_: u8 = 0;
    let mut v___x_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5107_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie;
                v___x_5108_ = lean_string_utf8_byte_size(v_s_5105_);
                lean_inc(v_p_5106_);
                v___x_5109_ = l_Lean_Data_Trie_matchPrefix___redArg(
                    v_s_5105_,
                    v___x_5107_,
                    v_p_5106_,
                    v___x_5108_,
                );
                if lean_obj_tag(v___x_5109_) == 1 {
                    v_val_5110_ = lean_ctor_get(v___x_5109_, 0);
                    lean_inc(v_val_5110_);
                    lean_dec_ref_known(v___x_5109_, 1);
                    v_fst_5111_ = lean_ctor_get(v_val_5110_, 0);
                    v_snd_5112_ = lean_ctor_get(v_val_5110_, 1);
                    v_isSharedCheck_5126_ = (!lean_is_exclusive(v_val_5110_)) as u8;
                    if v_isSharedCheck_5126_ == 0 {
                        v___x_5114_ = v_val_5110_;
                        v_isShared_5115_ = v_isSharedCheck_5126_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5112_);
                        lean_inc(v_fst_5111_);
                        lean_dec(v_val_5110_);
                        v___x_5114_ = lean_box(0);
                        v_isShared_5115_ = v_isSharedCheck_5126_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5109_);
                    v___x_5127_ =
                        l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__1;
                    v___x_5128_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_5128_, 0, v___x_5127_);
                    lean_ctor_set(v___x_5128_, 1, v_p_5106_);
                    return v___x_5128_;
                }
            }
            1 => {
                v___x_5116_ = lean_string_utf8_byte_size(v_fst_5111_);
                lean_dec(v_fst_5111_);
                v_p_x27_5117_ = lean_nat_add(v_p_5106_, v___x_5116_);
                v___x_5118_ = lean_string_is_valid_pos(v_s_5105_, v_p_x27_5117_);
                if v___x_5118_ == 0 {
                    lean_dec(v_p_x27_5117_);
                    lean_dec(v_snd_5112_);
                    v___x_5119_ =
                        l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___closed__0;
                    if v_isShared_5115_ == 0 {
                        lean_ctor_set_tag(v___x_5114_, 1);
                        lean_ctor_set(v___x_5114_, 1, v_p_5106_);
                        lean_ctor_set(v___x_5114_, 0, v___x_5119_);
                        v___x_5121_ = v___x_5114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5122_, 0, v___x_5119_);
                        lean_ctor_set(v_reuseFailAlloc_5122_, 1, v_p_5106_);
                        v___x_5121_ = v_reuseFailAlloc_5122_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_p_5106_);
                    if v_isShared_5115_ == 0 {
                        lean_ctor_set(v___x_5114_, 1, v_p_x27_5117_);
                        lean_ctor_set(v___x_5114_, 0, v_snd_5112_);
                        v___x_5124_ = v___x_5114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5125_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_snd_5112_);
                        lean_ctor_set(v_reuseFailAlloc_5125_, 1, v_p_x27_5117_);
                        v___x_5124_ = v_reuseFailAlloc_5125_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5121_;
            }
            3 => {
                return v___x_5124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM___boxed(
    mut v_s_5129_: *mut LeanObject,
    mut v_p_5130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5131_: *mut LeanObject = core::ptr::null_mut();
    v_res_5131_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_5129_, v_p_5130_);
    lean_dec_ref(v_s_5129_);
    return v_res_5131_;
}
pub unsafe fn l_Lake_ComparatorOp_ofString_x3f(mut v_s_5132_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    v___x_5133_ = lean_unsigned_to_nat(0);
    v___x_5134_ = l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_5132_, v___x_5133_);
    if lean_obj_tag(v___x_5134_) == 0 {
        let mut v_a_5135_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_5136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5138_: u8 = 0;
        v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
        lean_inc(v_a_5135_);
        v_a_5136_ = lean_ctor_get(v___x_5134_, 1);
        lean_inc(v_a_5136_);
        lean_dec_ref_known(v___x_5134_, 2);
        v___x_5137_ = lean_string_utf8_byte_size(v_s_5132_);
        v___x_5138_ = lean_nat_dec_eq(v_a_5136_, v___x_5137_);
        lean_dec(v_a_5136_);
        if v___x_5138_ == 0 {
            let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_5135_);
            v___x_5139_ = lean_box(0);
            return v___x_5139_;
        } else {
            let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
            v___x_5140_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_5140_, 0, v_a_5135_);
            return v___x_5140_;
        }
    } else {
        let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_5134_, 2);
        v___x_5141_ = lean_box(0);
        return v___x_5141_;
    }
}
pub unsafe fn l_Lake_ComparatorOp_ofString_x3f___boxed(
    mut v_s_5142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5143_: *mut LeanObject = core::ptr::null_mut();
    v_res_5143_ = l_Lake_ComparatorOp_ofString_x3f(v_s_5142_);
    lean_dec_ref(v_s_5142_);
    return v_res_5143_;
}
pub unsafe fn l_Lake_ComparatorOp_toString(mut v_self_5144_: u8) -> *mut LeanObject {
    match v_self_5144_ {
        0 => {
            let mut v___x_5145_: *mut LeanObject = core::ptr::null_mut();
            v___x_5145_ =
                l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__8;
            return v___x_5145_;
        }
        1 => {
            let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
            v___x_5146_ =
                l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__6;
            return v___x_5146_;
        }
        2 => {
            let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
            v___x_5147_ =
                l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__5;
            return v___x_5147_;
        }
        3 => {
            let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
            v___x_5148_ =
                l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__3;
            return v___x_5148_;
        }
        4 => {
            let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
            v___x_5149_ =
                l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__2;
            return v___x_5149_;
        }
        _ => {
            let mut v___x_5150_: *mut LeanObject = core::ptr::null_mut();
            v___x_5150_ =
                l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie___closed__0;
            return v___x_5150_;
        }
    }
}
pub unsafe fn l_Lake_ComparatorOp_toString___boxed(
    mut v_self_5151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_self_boxed_5152_: u8 = 0;
    let mut v_res_5153_: *mut LeanObject = core::ptr::null_mut();
    v_self_boxed_5152_ = (lean_unbox(v_self_5151_) as u8);
    v_res_5153_ = l_Lake_ComparatorOp_toString(v_self_boxed_5152_);
    return v_res_5153_;
}
pub unsafe fn _init_l_Lake_instReprVerComparator_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    v___x_5165_ = lean_unsigned_to_nat(7);
    v___x_5166_ = lean_nat_to_int(v___x_5165_);
    return v___x_5166_;
}
pub unsafe fn _init_l_Lake_instReprVerComparator_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    v___x_5170_ = lean_unsigned_to_nat(6);
    v___x_5171_ = lean_nat_to_int(v___x_5170_);
    return v___x_5171_;
}
pub unsafe fn _init_l_Lake_instReprVerComparator_repr___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    v___x_5175_ = lean_unsigned_to_nat(19);
    v___x_5176_ = lean_nat_to_int(v___x_5175_);
    return v___x_5176_;
}
pub unsafe fn l_Lake_instReprVerComparator_repr___redArg(
    mut v_x_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ver_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_op_5179_: u8 = 0;
    let mut v_includeSuffixes_5180_: u8 = 0;
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: u8 = 0;
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: *mut LeanObject = core::ptr::null_mut();
    v_ver_5178_ = lean_ctor_get(v_x_5177_, 0);
    lean_inc_ref(v_ver_5178_);
    v_op_5179_ = lean_ctor_get_uint8(
        v_x_5177_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_includeSuffixes_5180_ = lean_ctor_get_uint8(
        v_x_5177_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
    );
    lean_dec_ref(v_x_5177_);
    v___x_5181_ = l_Lake_instReprSemVerCore_repr___redArg___closed__5;
    v___x_5182_ = l_Lake_instReprVerComparator_repr___redArg___closed__3;
    v___x_5183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprVerComparator_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Lake_instReprVerComparator_repr___redArg___closed__4_once),
        _init_l_Lake_instReprVerComparator_repr___redArg___closed__4,
    );
    v___x_5184_ = lean_unsigned_to_nat(0);
    v___x_5185_ = l_Lake_instReprStdVer_repr___redArg(v_ver_5178_);
    v___x_5186_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5186_, 0, v___x_5183_);
    lean_ctor_set(v___x_5186_, 1, v___x_5185_);
    v___x_5187_ = 0;
    v___x_5188_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5188_, 0, v___x_5186_);
    lean_ctor_set_uint8(
        v___x_5188_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5187_,
    );
    v___x_5189_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5189_, 0, v___x_5182_);
    lean_ctor_set(v___x_5189_, 1, v___x_5188_);
    v___x_5190_ = l_Lake_instReprSemVerCore_repr___redArg___closed__9;
    v___x_5191_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5191_, 0, v___x_5189_);
    lean_ctor_set(v___x_5191_, 1, v___x_5190_);
    v___x_5192_ = lean_box(1);
    v___x_5193_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5193_, 0, v___x_5191_);
    lean_ctor_set(v___x_5193_, 1, v___x_5192_);
    v___x_5194_ = l_Lake_instReprVerComparator_repr___redArg___closed__6;
    v___x_5195_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5195_, 0, v___x_5193_);
    lean_ctor_set(v___x_5195_, 1, v___x_5194_);
    v___x_5196_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5196_, 0, v___x_5195_);
    lean_ctor_set(v___x_5196_, 1, v___x_5181_);
    v___x_5197_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprVerComparator_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lake_instReprVerComparator_repr___redArg___closed__7_once),
        _init_l_Lake_instReprVerComparator_repr___redArg___closed__7,
    );
    v___x_5198_ = l_Lake_instReprComparatorOp_repr(v_op_5179_, v___x_5184_);
    v___x_5199_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5199_, 0, v___x_5197_);
    lean_ctor_set(v___x_5199_, 1, v___x_5198_);
    v___x_5200_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5200_, 0, v___x_5199_);
    lean_ctor_set_uint8(
        v___x_5200_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5187_,
    );
    v___x_5201_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5201_, 0, v___x_5196_);
    lean_ctor_set(v___x_5201_, 1, v___x_5200_);
    v___x_5202_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5202_, 0, v___x_5201_);
    lean_ctor_set(v___x_5202_, 1, v___x_5190_);
    v___x_5203_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5203_, 0, v___x_5202_);
    lean_ctor_set(v___x_5203_, 1, v___x_5192_);
    v___x_5204_ = l_Lake_instReprVerComparator_repr___redArg___closed__9;
    v___x_5205_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5205_, 0, v___x_5203_);
    lean_ctor_set(v___x_5205_, 1, v___x_5204_);
    v___x_5206_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5206_, 0, v___x_5205_);
    lean_ctor_set(v___x_5206_, 1, v___x_5181_);
    v___x_5207_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprVerComparator_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lake_instReprVerComparator_repr___redArg___closed__10_once),
        _init_l_Lake_instReprVerComparator_repr___redArg___closed__10,
    );
    v___x_5208_ = l_Bool_repr___redArg(v_includeSuffixes_5180_);
    v___x_5209_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5209_, 0, v___x_5207_);
    lean_ctor_set(v___x_5209_, 1, v___x_5208_);
    v___x_5210_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5210_, 0, v___x_5209_);
    lean_ctor_set_uint8(
        v___x_5210_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5187_,
    );
    v___x_5211_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5211_, 0, v___x_5206_);
    lean_ctor_set(v___x_5211_, 1, v___x_5210_);
    v___x_5212_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__16_once),
        _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16,
    );
    v___x_5213_ = l_Lake_instReprSemVerCore_repr___redArg___closed__17;
    v___x_5214_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5214_, 0, v___x_5213_);
    lean_ctor_set(v___x_5214_, 1, v___x_5211_);
    v___x_5215_ = l_Lake_instReprSemVerCore_repr___redArg___closed__18;
    v___x_5216_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_5216_, 0, v___x_5214_);
    lean_ctor_set(v___x_5216_, 1, v___x_5215_);
    v___x_5217_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_5217_, 0, v___x_5212_);
    lean_ctor_set(v___x_5217_, 1, v___x_5216_);
    v___x_5218_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_5218_, 0, v___x_5217_);
    lean_ctor_set_uint8(
        v___x_5218_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5187_,
    );
    return v___x_5218_;
}
pub unsafe fn l_Lake_instReprVerComparator_repr(
    mut v_x_5219_: *mut LeanObject,
    mut v_prec_5220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    v___x_5221_ = l_Lake_instReprVerComparator_repr___redArg(v_x_5219_);
    return v___x_5221_;
}
pub unsafe fn l_Lake_instReprVerComparator_repr___boxed(
    mut v_x_5222_: *mut LeanObject,
    mut v_prec_5223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5224_: *mut LeanObject = core::ptr::null_mut();
    v_res_5224_ = l_Lake_instReprVerComparator_repr(v_x_5222_, v_prec_5223_);
    lean_dec(v_prec_5223_);
    return v_res_5224_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(
    mut v_s_5238_: *mut LeanObject,
    mut v_a_5239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5245_: u8 = 0;
    let mut v___x_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: u8 = 0;
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5256_: u8 = 0;
    let mut v_val_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: u8 = 0;
    let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: u8 = 0;
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5274_: u8 = 0;
    let mut v_unused_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5287_: u8 = 0;
    let mut v_unused_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5297_: u8 = 0;
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut v_a_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_5239_);
                v___x_5240_ =
                    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM(v_s_5238_, v_a_5239_);
                if lean_obj_tag(v___x_5240_) == 0 {
                    v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
                    v_a_5242_ = lean_ctor_get(v___x_5240_, 1);
                    v_isSharedCheck_5307_ = (!lean_is_exclusive(v___x_5240_)) as u8;
                    if v_isSharedCheck_5307_ == 0 {
                        v___x_5244_ = v___x_5240_;
                        v_isShared_5245_ = v_isSharedCheck_5307_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5242_);
                        lean_inc(v_a_5241_);
                        lean_dec(v___x_5240_);
                        v___x_5244_ = lean_box(0);
                        v_isShared_5245_ = v_isSharedCheck_5307_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5239_);
                    lean_dec_ref(v_s_5238_);
                    v_a_5308_ = lean_ctor_get(v___x_5240_, 0);
                    v_a_5309_ = lean_ctor_get(v___x_5240_, 1);
                    v_isSharedCheck_5316_ = (!lean_is_exclusive(v___x_5240_)) as u8;
                    if v_isSharedCheck_5316_ == 0 {
                        v___x_5311_ = v___x_5240_;
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_5309_);
                        lean_inc(v_a_5308_);
                        lean_dec(v___x_5240_);
                        v___x_5311_ = lean_box(0);
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5246_ = lean_string_utf8_byte_size(v_s_5238_);
                v___x_5247_ = lean_nat_dec_eq(v_a_5242_, v___x_5246_);
                if v___x_5247_ == 0 {
                    lean_del_object(v___x_5244_);
                    lean_dec(v_a_5239_);
                    lean_inc_ref(v_s_5238_);
                    v___x_5248_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM(
                        v_s_5238_, v_a_5242_,
                    );
                    if lean_obj_tag(v___x_5248_) == 0 {
                        v_a_5249_ = lean_ctor_get(v___x_5248_, 0);
                        lean_inc(v_a_5249_);
                        v_a_5250_ = lean_ctor_get(v___x_5248_, 1);
                        lean_inc(v_a_5250_);
                        lean_dec_ref_known(v___x_5248_, 2);
                        v___x_5251_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr_x3f(
                            v_s_5238_, v_a_5250_,
                        );
                        lean_dec_ref(v_s_5238_);
                        v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
                        lean_inc(v_a_5252_);
                        if lean_obj_tag(v_a_5252_) == 1 {
                            v_a_5253_ = lean_ctor_get(v___x_5251_, 1);
                            v_isSharedCheck_5274_ = (!lean_is_exclusive(v___x_5251_)) as u8;
                            if v_isSharedCheck_5274_ == 0 {
                                v_unused_5275_ = lean_ctor_get(v___x_5251_, 0);
                                lean_dec(v_unused_5275_);
                                v___x_5255_ = v___x_5251_;
                                v_isShared_5256_ = v_isSharedCheck_5274_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_5253_);
                                lean_dec(v___x_5251_);
                                v___x_5255_ = lean_box(0);
                                v_isShared_5256_ = v_isSharedCheck_5274_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5252_);
                            v_a_5276_ = lean_ctor_get(v___x_5251_, 1);
                            v_isSharedCheck_5287_ = (!lean_is_exclusive(v___x_5251_)) as u8;
                            if v_isSharedCheck_5287_ == 0 {
                                v_unused_5288_ = lean_ctor_get(v___x_5251_, 0);
                                lean_dec(v_unused_5288_);
                                v___x_5278_ = v___x_5251_;
                                v_isShared_5279_ = v_isSharedCheck_5287_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_5276_);
                                lean_dec(v___x_5251_);
                                v___x_5278_ = lean_box(0);
                                v_isShared_5279_ = v_isSharedCheck_5287_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5241_);
                        lean_dec_ref(v_s_5238_);
                        v_a_5289_ = lean_ctor_get(v___x_5248_, 0);
                        v_a_5290_ = lean_ctor_get(v___x_5248_, 1);
                        v_isSharedCheck_5297_ = (!lean_is_exclusive(v___x_5248_)) as u8;
                        if v_isSharedCheck_5297_ == 0 {
                            v___x_5292_ = v___x_5248_;
                            v_isShared_5293_ = v_isSharedCheck_5297_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5290_);
                            lean_inc(v_a_5289_);
                            lean_dec(v___x_5248_);
                            v___x_5292_ = lean_box(0);
                            v_isShared_5293_ = v_isSharedCheck_5297_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_5241_);
                    v___x_5298_ =
                        l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__0;
                    v___x_5299_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5299_, 0, v_s_5238_);
                    lean_ctor_set(v___x_5299_, 1, v_a_5239_);
                    lean_ctor_set(v___x_5299_, 2, v___x_5246_);
                    v___x_5300_ = l_String_Slice_toString(v___x_5299_);
                    lean_dec_ref_known(v___x_5299_, 3);
                    v___x_5301_ = lean_string_append(v___x_5298_, v___x_5300_);
                    lean_dec_ref(v___x_5300_);
                    v___x_5302_ =
                        l___private_Lake_Util_Version_0__Lake_VerComparator_parseM___closed__1;
                    v___x_5303_ = lean_string_append(v___x_5301_, v___x_5302_);
                    if v_isShared_5245_ == 0 {
                        lean_ctor_set_tag(v___x_5244_, 1);
                        lean_ctor_set(v___x_5244_, 0, v___x_5303_);
                        v___x_5305_ = v___x_5244_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5303_);
                        lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_a_5242_);
                        v___x_5305_ = v_reuseFailAlloc_5306_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v_val_5257_ = lean_ctor_get(v_a_5252_, 0);
                lean_inc(v_val_5257_);
                lean_dec_ref_known(v_a_5252_, 1);
                v___x_5258_ = lean_string_utf8_byte_size(v_val_5257_);
                v___x_5259_ = lean_unsigned_to_nat(0);
                v___x_5260_ = lean_nat_dec_eq(v___x_5258_, v___x_5259_);
                if v___x_5260_ == 0 {
                    v___x_5261_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5261_, 0, v_a_5249_);
                    lean_ctor_set(v___x_5261_, 1, v_val_5257_);
                    v___x_5262_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_5262_, 0, v___x_5261_);
                    v___x_5263_ = (lean_unbox(v_a_5241_) as u8);
                    lean_dec(v_a_5241_);
                    lean_ctor_set_uint8(
                        v___x_5262_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5263_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5262_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v___x_5260_,
                    );
                    if v_isShared_5256_ == 0 {
                        lean_ctor_set(v___x_5255_, 0, v___x_5262_);
                        v___x_5265_ = v___x_5255_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5262_);
                        lean_ctor_set(v_reuseFailAlloc_5266_, 1, v_a_5253_);
                        v___x_5265_ = v_reuseFailAlloc_5266_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_val_5257_);
                    v___x_5267_ =
                        l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                    v___x_5268_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5268_, 0, v_a_5249_);
                    lean_ctor_set(v___x_5268_, 1, v___x_5267_);
                    v___x_5269_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_5269_, 0, v___x_5268_);
                    v___x_5270_ = (lean_unbox(v_a_5241_) as u8);
                    lean_dec(v_a_5241_);
                    lean_ctor_set_uint8(
                        v___x_5269_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5270_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5269_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v___x_5260_,
                    );
                    if v_isShared_5256_ == 0 {
                        lean_ctor_set(v___x_5255_, 0, v___x_5269_);
                        v___x_5272_ = v___x_5255_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5273_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5273_, 0, v___x_5269_);
                        lean_ctor_set(v_reuseFailAlloc_5273_, 1, v_a_5253_);
                        v___x_5272_ = v_reuseFailAlloc_5273_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5265_;
            }
            4 => {
                return v___x_5272_;
            }
            5 => {
                v___x_5280_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                v___x_5281_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5281_, 0, v_a_5249_);
                lean_ctor_set(v___x_5281_, 1, v___x_5280_);
                v___x_5282_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_5282_, 0, v___x_5281_);
                v___x_5283_ = (lean_unbox(v_a_5241_) as u8);
                lean_dec(v_a_5241_);
                lean_ctor_set_uint8(
                    v___x_5282_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5283_,
                );
                lean_ctor_set_uint8(
                    v___x_5282_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_5247_,
                );
                if v_isShared_5279_ == 0 {
                    lean_ctor_set(v___x_5278_, 0, v___x_5282_);
                    v___x_5285_ = v___x_5278_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5286_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5286_, 0, v___x_5282_);
                    lean_ctor_set(v_reuseFailAlloc_5286_, 1, v_a_5276_);
                    v___x_5285_ = v_reuseFailAlloc_5286_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5285_;
            }
            7 => {
                if v_isShared_5293_ == 0 {
                    v___x_5295_ = v___x_5292_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5289_);
                    lean_ctor_set(v_reuseFailAlloc_5296_, 1, v_a_5290_);
                    v___x_5295_ = v_reuseFailAlloc_5296_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5295_;
            }
            9 => {
                return v___x_5305_;
            }
            10 => {
                if v_isShared_5312_ == 0 {
                    v___x_5314_ = v___x_5311_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5308_);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 1, v_a_5309_);
                    v___x_5314_ = v_reuseFailAlloc_5315_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_VerComparator_parse(mut v_s_5317_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    v___x_5318_ = lean_unsigned_to_nat(0);
    v___x_5319_ = lean_string_utf8_byte_size(v_s_5317_);
    lean_inc_ref(v_s_5317_);
    v___x_5320_ =
        l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(v_s_5317_, v___x_5318_);
    if lean_obj_tag(v___x_5320_) == 0 {
        let mut v_a_5321_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_5322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5323_: u8 = 0;
        v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
        lean_inc(v_a_5321_);
        v_a_5322_ = lean_ctor_get(v___x_5320_, 1);
        lean_inc(v_a_5322_);
        lean_dec_ref_known(v___x_5320_, 2);
        v___x_5323_ = lean_nat_dec_eq(v_a_5322_, v___x_5319_);
        if v___x_5323_ == 0 {
            let mut v_tail_5324_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5327_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_5321_);
            v_tail_5324_ = lean_string_utf8_extract(v_s_5317_, v_a_5322_, v___x_5319_);
            lean_dec(v_a_5322_);
            lean_dec_ref(v_s_5317_);
            v___x_5325_ = l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0;
            v___x_5326_ = lean_string_append(v___x_5325_, v_tail_5324_);
            lean_dec_ref(v_tail_5324_);
            v___x_5327_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_5327_, 0, v___x_5326_);
            return v___x_5327_;
        } else {
            let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_5322_);
            lean_dec_ref(v_s_5317_);
            v___x_5328_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_5328_, 0, v_a_5321_);
            return v___x_5328_;
        }
    } else {
        let mut v_a_5329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5330_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_s_5317_);
        v_a_5329_ = lean_ctor_get(v___x_5320_, 0);
        lean_inc(v_a_5329_);
        lean_dec_ref_known(v___x_5320_, 2);
        v___x_5330_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5330_, 0, v_a_5329_);
        return v___x_5330_;
    }
}
pub unsafe fn l_Lake_VerComparator_test(
    mut v_self_5331_: *mut LeanObject,
    mut v_ver_5332_: *mut LeanObject,
) -> u8 {
    let mut v___y_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5335_: u8 = 0;
    let mut v___y_5336_: u8 = 0;
    let mut v___y_5337_: u8 = 0;
    let mut v___y_5338_: u8 = 0;
    let mut v___y_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5340_: u8 = 0;
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: u8 = 0;
    let mut v___x_5343_: u8 = 0;
    let mut v___y_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5346_: u8 = 0;
    let mut v___y_5347_: u8 = 0;
    let mut v___y_5348_: u8 = 0;
    let mut v___y_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5350_: u8 = 0;
    let mut v___x_5351_: u8 = 0;
    let mut v___x_5352_: u8 = 0;
    let mut v___x_5353_: u8 = 0;
    let mut v___y_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5356_: u8 = 0;
    let mut v___y_5357_: u8 = 0;
    let mut v___y_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5359_: u8 = 0;
    let mut v___x_5360_: u8 = 0;
    let mut v___x_5361_: u8 = 0;
    let mut v___x_5362_: u8 = 0;
    let mut v___y_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5365_: u8 = 0;
    let mut v___y_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5367_: u8 = 0;
    let mut v___x_5368_: u8 = 0;
    let mut v___x_5369_: u8 = 0;
    let mut v___x_5370_: u8 = 0;
    let mut v_ver_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_op_5372_: u8 = 0;
    let mut v_includeSuffixes_5373_: u8 = 0;
    let mut v_ver_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: u8 = 0;
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: u8 = 0;
    let mut v_toSemVerCore_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: u8 = 0;
    let mut v_toSemVerCore_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specialDescr_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: u8 = 0;
    let mut v___x_5386_: u8 = 0;
    let mut v___x_5387_: u8 = 0;
    let mut v___x_5388_: u8 = 0;
    let mut v___x_5389_: u8 = 0;
    let mut v___x_5390_: u8 = 0;
    let mut v___x_5391_: u8 = 0;
    let mut v___x_5392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ver_5371_ = lean_ctor_get(v_self_5331_, 0);
                v_op_5372_ = lean_ctor_get_uint8(
                    v_self_5331_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_includeSuffixes_5373_ = lean_ctor_get_uint8(
                    v_self_5331_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                if v_includeSuffixes_5373_ == 0 {
                    v_toSemVerCore_5379_ = lean_ctor_get(v_ver_5332_, 0);
                    v_specialDescr_5380_ = lean_ctor_get(v_ver_5332_, 1);
                    v___x_5381_ =
                        l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                    v___x_5382_ = lean_string_dec_eq(v_specialDescr_5380_, v___x_5381_);
                    if v___x_5382_ == 0 {
                        v_toSemVerCore_5383_ = lean_ctor_get(v_ver_5371_, 0);
                        v_specialDescr_5384_ = lean_ctor_get(v_ver_5371_, 1);
                        v___x_5385_ = lean_string_dec_eq(v_specialDescr_5384_, v___x_5381_);
                        if v___x_5385_ == 0 {
                            v___x_5386_ = l_Lake_instDecidableEqSemVerCore_decEq(
                                v_toSemVerCore_5383_,
                                v_toSemVerCore_5379_,
                            );
                            if v___x_5386_ == 0 {
                                return v_includeSuffixes_5373_;
                            } else {
                                match v_op_5372_ {
                                    0 => {
                                        v___x_5387_ = lean_string_dec_lt(
                                            v_specialDescr_5380_,
                                            v_specialDescr_5384_,
                                        );
                                        return v___x_5387_;
                                    }
                                    1 => {
                                        v___x_5388_ = l_String_decLE(
                                            v_specialDescr_5380_,
                                            v_specialDescr_5384_,
                                        );
                                        return v___x_5388_;
                                    }
                                    2 => {
                                        v___x_5389_ = lean_string_dec_lt(
                                            v_specialDescr_5384_,
                                            v_specialDescr_5380_,
                                        );
                                        return v___x_5389_;
                                    }
                                    3 => {
                                        v___x_5390_ = l_String_decLE(
                                            v_specialDescr_5384_,
                                            v_specialDescr_5380_,
                                        );
                                        return v___x_5390_;
                                    }
                                    4 => {
                                        v___x_5391_ = lean_string_dec_eq(
                                            v_specialDescr_5380_,
                                            v_specialDescr_5384_,
                                        );
                                        return v___x_5391_;
                                    }
                                    _ => {
                                        v___x_5392_ = lean_string_dec_eq(
                                            v_specialDescr_5380_,
                                            v_specialDescr_5384_,
                                        );
                                        if v___x_5392_ == 0 {
                                            return v___x_5386_;
                                        } else {
                                            return v___x_5385_;
                                        }
                                    }
                                }
                            }
                        } else {
                            return v_includeSuffixes_5373_;
                        }
                    } else {
                        v_ver_5375_ = v_ver_5332_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_ver_5375_ = v_ver_5332_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_5341_ = l_Lake_instDecidableEqStdVer_decEq(v___y_5334_, v___y_5339_);
                match v___y_5336_ {
                    0 => {
                        return v___y_5335_;
                    }
                    1 => {
                        return v___y_5338_;
                    }
                    2 => {
                        return v___y_5337_;
                    }
                    3 => {
                        return v___y_5340_;
                    }
                    4 => {
                        return v___x_5341_;
                    }
                    _ => {
                        if v___x_5341_ == 0 {
                            v___x_5342_ = 1;
                            return v___x_5342_;
                        } else {
                            v___x_5343_ = 0;
                            return v___x_5343_;
                        }
                    }
                }
            }
            2 => {
                v___x_5351_ = l_Lake_StdVer_compare(v___y_5349_, v___y_5345_);
                if v___x_5351_ == 2 {
                    v___x_5352_ = 0;
                    v___y_5334_ = v___y_5345_;
                    v___y_5335_ = v___y_5346_;
                    v___y_5336_ = v___y_5347_;
                    v___y_5337_ = v___y_5350_;
                    v___y_5338_ = v___y_5348_;
                    v___y_5339_ = v___y_5349_;
                    v___y_5340_ = v___x_5352_;
                    state = 1;
                    continue;
                } else {
                    v___x_5353_ = 1;
                    v___y_5334_ = v___y_5345_;
                    v___y_5335_ = v___y_5346_;
                    v___y_5336_ = v___y_5347_;
                    v___y_5337_ = v___y_5350_;
                    v___y_5338_ = v___y_5348_;
                    v___y_5339_ = v___y_5349_;
                    v___y_5340_ = v___x_5353_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5360_ = l_Lake_StdVer_compare(v___y_5358_, v___y_5355_);
                if v___x_5360_ == 0 {
                    v___x_5361_ = 1;
                    v___y_5345_ = v___y_5355_;
                    v___y_5346_ = v___y_5356_;
                    v___y_5347_ = v___y_5357_;
                    v___y_5348_ = v___y_5359_;
                    v___y_5349_ = v___y_5358_;
                    v___y_5350_ = v___x_5361_;
                    state = 2;
                    continue;
                } else {
                    v___x_5362_ = 0;
                    v___y_5345_ = v___y_5355_;
                    v___y_5346_ = v___y_5356_;
                    v___y_5347_ = v___y_5357_;
                    v___y_5348_ = v___y_5359_;
                    v___y_5349_ = v___y_5358_;
                    v___y_5350_ = v___x_5362_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_5368_ = l_Lake_StdVer_compare(v___y_5364_, v___y_5366_);
                if v___x_5368_ == 2 {
                    v___x_5369_ = 0;
                    v___y_5355_ = v___y_5364_;
                    v___y_5356_ = v___y_5367_;
                    v___y_5357_ = v___y_5365_;
                    v___y_5358_ = v___y_5366_;
                    v___y_5359_ = v___x_5369_;
                    state = 3;
                    continue;
                } else {
                    v___x_5370_ = 1;
                    v___y_5355_ = v___y_5364_;
                    v___y_5356_ = v___y_5367_;
                    v___y_5357_ = v___y_5365_;
                    v___y_5358_ = v___y_5366_;
                    v___y_5359_ = v___x_5370_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_5376_ = l_Lake_StdVer_compare(v_ver_5375_, v_ver_5371_);
                if v___x_5376_ == 0 {
                    v___x_5377_ = 1;
                    v___y_5364_ = v_ver_5375_;
                    v___y_5365_ = v_op_5372_;
                    v___y_5366_ = v_ver_5371_;
                    v___y_5367_ = v___x_5377_;
                    state = 4;
                    continue;
                } else {
                    v___x_5378_ = 0;
                    v___y_5364_ = v_ver_5375_;
                    v___y_5365_ = v_op_5372_;
                    v___y_5366_ = v_ver_5371_;
                    v___y_5367_ = v___x_5378_;
                    state = 4;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_VerComparator_test___boxed(
    mut v_self_5393_: *mut LeanObject,
    mut v_ver_5394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5395_: u8 = 0;
    let mut v_r_5396_: *mut LeanObject = core::ptr::null_mut();
    v_res_5395_ = l_Lake_VerComparator_test(v_self_5393_, v_ver_5394_);
    lean_dec_ref(v_ver_5394_);
    lean_dec_ref(v_self_5393_);
    v_r_5396_ = lean_box((v_res_5395_) as usize);
    return v_r_5396_;
}
pub unsafe fn l_Lake_VerComparator_toString(mut v_self_5397_: *mut LeanObject) -> *mut LeanObject {
    let mut v_ver_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_op_5399_: u8 = 0;
    let mut v_includeSuffixes_5400_: u8 = 0;
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    v_ver_5398_ = lean_ctor_get(v_self_5397_, 0);
    lean_inc_ref(v_ver_5398_);
    v_op_5399_ = lean_ctor_get_uint8(
        v_self_5397_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
    );
    v_includeSuffixes_5400_ = lean_ctor_get_uint8(
        v_self_5397_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
    );
    lean_dec_ref(v_self_5397_);
    v___x_5401_ = l_Lake_ComparatorOp_toString(v_op_5399_);
    v___x_5402_ = l_Lake_StdVer_toString(v_ver_5398_);
    v___x_5403_ = lean_string_append(v___x_5401_, v___x_5402_);
    lean_dec_ref(v___x_5402_);
    if v_includeSuffixes_5400_ == 0 {
        return v___x_5403_;
    } else {
        let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
        v___x_5404_ = l_Lake_StdVer_toString___closed__0;
        v___x_5405_ = lean_string_append(v___x_5403_, v___x_5404_);
        return v___x_5405_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_x_5408_: *mut LeanObject,
    mut v_x_5409_: *mut LeanObject,
    mut v_x_5410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5415_: u8 = 0;
    let mut v___x_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5410_) == 0 {
                    lean_dec(v_x_5408_);
                    return v_x_5409_;
                } else {
                    v_head_5411_ = lean_ctor_get(v_x_5410_, 0);
                    v_tail_5412_ = lean_ctor_get(v_x_5410_, 1);
                    v_isSharedCheck_5422_ = (!lean_is_exclusive(v_x_5410_)) as u8;
                    if v_isSharedCheck_5422_ == 0 {
                        v___x_5414_ = v_x_5410_;
                        v_isShared_5415_ = v_isSharedCheck_5422_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5412_);
                        lean_inc(v_head_5411_);
                        lean_dec(v_x_5410_);
                        v___x_5414_ = lean_box(0);
                        v_isShared_5415_ = v_isSharedCheck_5422_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5408_);
                if v_isShared_5415_ == 0 {
                    lean_ctor_set_tag(v___x_5414_, 5);
                    lean_ctor_set(v___x_5414_, 1, v_x_5408_);
                    lean_ctor_set(v___x_5414_, 0, v_x_5409_);
                    v___x_5417_ = v___x_5414_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5421_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5421_, 0, v_x_5409_);
                    lean_ctor_set(v_reuseFailAlloc_5421_, 1, v_x_5408_);
                    v___x_5417_ = v_reuseFailAlloc_5421_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5418_ = l_Lake_instReprVerComparator_repr___redArg(v_head_5411_);
                v___x_5419_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5419_, 0, v___x_5417_);
                lean_ctor_set(v___x_5419_, 1, v___x_5418_);
                v_x_5409_ = v___x_5419_;
                v_x_5410_ = v_tail_5412_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(
    mut v_x_5423_: *mut LeanObject,
    mut v_x_5424_: *mut LeanObject,
    mut v_x_5425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5430_: u8 = 0;
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5425_) == 0 {
                    lean_dec(v_x_5423_);
                    return v_x_5424_;
                } else {
                    v_head_5426_ = lean_ctor_get(v_x_5425_, 0);
                    v_tail_5427_ = lean_ctor_get(v_x_5425_, 1);
                    v_isSharedCheck_5437_ = (!lean_is_exclusive(v_x_5425_)) as u8;
                    if v_isSharedCheck_5437_ == 0 {
                        v___x_5429_ = v_x_5425_;
                        v_isShared_5430_ = v_isSharedCheck_5437_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5427_);
                        lean_inc(v_head_5426_);
                        lean_dec(v_x_5425_);
                        v___x_5429_ = lean_box(0);
                        v_isShared_5430_ = v_isSharedCheck_5437_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5423_);
                if v_isShared_5430_ == 0 {
                    lean_ctor_set_tag(v___x_5429_, 5);
                    lean_ctor_set(v___x_5429_, 1, v_x_5423_);
                    lean_ctor_set(v___x_5429_, 0, v_x_5424_);
                    v___x_5432_ = v___x_5429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5436_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_x_5424_);
                    lean_ctor_set(v_reuseFailAlloc_5436_, 1, v_x_5423_);
                    v___x_5432_ = v_reuseFailAlloc_5436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5433_ = l_Lake_instReprVerComparator_repr___redArg(v_head_5426_);
                v___x_5434_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5434_, 0, v___x_5432_);
                lean_ctor_set(v___x_5434_, 1, v___x_5433_);
                v___x_5435_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2_spec__4(v_x_5423_, v___x_5434_, v_tail_5427_);
                return v___x_5435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(
    mut v_x_5438_: *mut LeanObject,
    mut v_x_5439_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5438_) == 0 {
        let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5439_);
        v___x_5440_ = lean_box(0);
        return v___x_5440_;
    } else {
        let mut v_tail_5441_: *mut LeanObject = core::ptr::null_mut();
        v_tail_5441_ = lean_ctor_get(v_x_5438_, 1);
        if lean_obj_tag(v_tail_5441_) == 0 {
            let mut v_head_5442_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_5439_);
            v_head_5442_ = lean_ctor_get(v_x_5438_, 0);
            lean_inc(v_head_5442_);
            lean_dec_ref_known(v_x_5438_, 2);
            v___x_5443_ = l_Lake_instReprVerComparator_repr___redArg(v_head_5442_);
            return v___x_5443_;
        } else {
            let mut v_head_5444_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_5441_);
            v_head_5444_ = lean_ctor_get(v_x_5438_, 0);
            lean_inc(v_head_5444_);
            lean_dec_ref_known(v_x_5438_, 2);
            v___x_5445_ = l_Lake_instReprVerComparator_repr___redArg(v_head_5444_);
            v___x_5446_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1_spec__2(v_x_5439_, v___x_5445_, v_tail_5441_);
            return v___x_5446_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    v___x_5452_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__0;
    v___x_5453_ = lean_string_length(v___x_5452_);
    return v___x_5453_;
}
pub unsafe fn _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    v___x_5454_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3_once), _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__3);
    v___x_5455_ = lean_nat_to_int(v___x_5454_);
    return v___x_5455_;
}
pub unsafe fn l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(
    mut v_xs_5463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: u8 = 0;
    v___x_5464_ = lean_array_get_size(v_xs_5463_);
    v___x_5465_ = lean_unsigned_to_nat(0);
    v___x_5466_ = lean_nat_dec_eq(v___x_5464_, v___x_5465_);
    if v___x_5466_ == 0 {
        let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
        v___x_5467_ = lean_array_to_list(v_xs_5463_);
        v___x_5468_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1;
        v___x_5469_ = l_Std_Format_joinSep___at___00Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0_spec__1(v___x_5467_, v___x_5468_);
        v___x_5470_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once), _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
        v___x_5471_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5;
        v___x_5472_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5472_, 0, v___x_5471_);
        lean_ctor_set(v___x_5472_, 1, v___x_5469_);
        v___x_5473_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6;
        v___x_5474_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5474_, 0, v___x_5472_);
        lean_ctor_set(v___x_5474_, 1, v___x_5473_);
        v___x_5475_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_5475_, 0, v___x_5470_);
        lean_ctor_set(v___x_5475_, 1, v___x_5474_);
        v___x_5476_ = l_Std_Format_fill(v___x_5475_);
        return v___x_5476_;
    } else {
        let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_5463_);
        v___x_5477_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8;
        return v___x_5477_;
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(
    mut v_x_5478_: *mut LeanObject,
    mut v_x_5479_: *mut LeanObject,
    mut v_x_5480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5485_: u8 = 0;
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5480_) == 0 {
                    lean_dec(v_x_5478_);
                    return v_x_5479_;
                } else {
                    v_head_5481_ = lean_ctor_get(v_x_5480_, 0);
                    v_tail_5482_ = lean_ctor_get(v_x_5480_, 1);
                    v_isSharedCheck_5492_ = (!lean_is_exclusive(v_x_5480_)) as u8;
                    if v_isSharedCheck_5492_ == 0 {
                        v___x_5484_ = v_x_5480_;
                        v_isShared_5485_ = v_isSharedCheck_5492_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5482_);
                        lean_inc(v_head_5481_);
                        lean_dec(v_x_5480_);
                        v___x_5484_ = lean_box(0);
                        v_isShared_5485_ = v_isSharedCheck_5492_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_5478_);
                if v_isShared_5485_ == 0 {
                    lean_ctor_set_tag(v___x_5484_, 5);
                    lean_ctor_set(v___x_5484_, 1, v_x_5478_);
                    lean_ctor_set(v___x_5484_, 0, v_x_5479_);
                    v___x_5487_ = v___x_5484_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_x_5479_);
                    lean_ctor_set(v_reuseFailAlloc_5491_, 1, v_x_5478_);
                    v___x_5487_ = v_reuseFailAlloc_5491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5488_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_5481_);
                v___x_5489_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5489_, 0, v___x_5487_);
                lean_ctor_set(v___x_5489_, 1, v___x_5488_);
                v_x_5479_ = v___x_5489_;
                v_x_5480_ = v_tail_5482_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(
    mut v_x_5493_: *mut LeanObject,
    mut v_x_5494_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5493_) == 0 {
        let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_5494_);
        v___x_5495_ = lean_box(0);
        return v___x_5495_;
    } else {
        let mut v_tail_5496_: *mut LeanObject = core::ptr::null_mut();
        v_tail_5496_ = lean_ctor_get(v_x_5493_, 1);
        if lean_obj_tag(v_tail_5496_) == 0 {
            let mut v_head_5497_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_5494_);
            v_head_5497_ = lean_ctor_get(v_x_5493_, 0);
            lean_inc(v_head_5497_);
            lean_dec_ref_known(v_x_5493_, 2);
            v___x_5498_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_5497_);
            return v___x_5498_;
        } else {
            let mut v_head_5499_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_5496_);
            v_head_5499_ = lean_ctor_get(v_x_5493_, 0);
            lean_inc(v_head_5499_);
            lean_dec_ref_known(v_x_5493_, 2);
            v___x_5500_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0(v_head_5499_);
            v___x_5501_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1_spec__3(v_x_5494_, v___x_5500_, v_tail_5496_);
            return v___x_5501_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(
    mut v_xs_5502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: u8 = 0;
    v___x_5503_ = lean_array_get_size(v_xs_5502_);
    v___x_5504_ = lean_unsigned_to_nat(0);
    v___x_5505_ = lean_nat_dec_eq(v___x_5503_, v___x_5504_);
    if v___x_5505_ == 0 {
        let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5511_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
        v___x_5506_ = lean_array_to_list(v_xs_5502_);
        v___x_5507_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__1;
        v___x_5508_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__1(v___x_5506_, v___x_5507_);
        v___x_5509_ = lean_obj_once(core::ptr::addr_of_mut!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4_once), _init_l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__4);
        v___x_5510_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__5;
        v___x_5511_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5511_, 0, v___x_5510_);
        lean_ctor_set(v___x_5511_, 1, v___x_5508_);
        v___x_5512_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__6;
        v___x_5513_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_5513_, 0, v___x_5511_);
        lean_ctor_set(v___x_5513_, 1, v___x_5512_);
        v___x_5514_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_5514_, 0, v___x_5509_);
        lean_ctor_set(v___x_5514_, 1, v___x_5513_);
        v___x_5515_ = l_Std_Format_fill(v___x_5514_);
        return v___x_5515_;
    } else {
        let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_5502_);
        v___x_5516_ = l_Array_repr___at___00Array_repr___at___00Lake_instReprVerRange_repr_spec__0_spec__0___closed__8;
        return v___x_5516_;
    }
}
pub unsafe fn _init_l_Lake_instReprVerRange_repr___redArg___closed__4() -> *mut LeanObject {
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    v___x_5526_ = lean_unsigned_to_nat(12);
    v___x_5527_ = lean_nat_to_int(v___x_5526_);
    return v___x_5527_;
}
pub unsafe fn _init_l_Lake_instReprVerRange_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    v___x_5531_ = lean_unsigned_to_nat(11);
    v___x_5532_ = lean_nat_to_int(v___x_5531_);
    return v___x_5532_;
}
pub unsafe fn l_Lake_instReprVerRange_repr___redArg(
    mut v_x_5533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toString_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_clauses_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5538_: u8 = 0;
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: u8 = 0;
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5569_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toString_5534_ = lean_ctor_get(v_x_5533_, 0);
                v_clauses_5535_ = lean_ctor_get(v_x_5533_, 1);
                v_isSharedCheck_5569_ = (!lean_is_exclusive(v_x_5533_)) as u8;
                if v_isSharedCheck_5569_ == 0 {
                    v___x_5537_ = v_x_5533_;
                    v_isShared_5538_ = v_isSharedCheck_5569_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_clauses_5535_);
                    lean_inc(v_toString_5534_);
                    lean_dec(v_x_5533_);
                    v___x_5537_ = lean_box(0);
                    v_isShared_5538_ = v_isSharedCheck_5569_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5539_ = l_Lake_instReprSemVerCore_repr___redArg___closed__5;
                v___x_5540_ = l_Lake_instReprVerRange_repr___redArg___closed__3;
                v___x_5541_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instReprVerRange_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(l_Lake_instReprVerRange_repr___redArg___closed__4_once),
                    _init_l_Lake_instReprVerRange_repr___redArg___closed__4,
                );
                v___x_5542_ = l_String_quote(v_toString_5534_);
                v___x_5543_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_5543_, 0, v___x_5542_);
                if v_isShared_5538_ == 0 {
                    lean_ctor_set_tag(v___x_5537_, 4);
                    lean_ctor_set(v___x_5537_, 1, v___x_5543_);
                    lean_ctor_set(v___x_5537_, 0, v___x_5541_);
                    v___x_5545_ = v___x_5537_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5568_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5541_);
                    lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5543_);
                    v___x_5545_ = v_reuseFailAlloc_5568_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5546_ = 0;
                v___x_5547_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5547_, 0, v___x_5545_);
                lean_ctor_set_uint8(
                    v___x_5547_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5546_,
                );
                v___x_5548_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5548_, 0, v___x_5540_);
                lean_ctor_set(v___x_5548_, 1, v___x_5547_);
                v___x_5549_ = l_Lake_instReprSemVerCore_repr___redArg___closed__9;
                v___x_5550_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5550_, 0, v___x_5548_);
                lean_ctor_set(v___x_5550_, 1, v___x_5549_);
                v___x_5551_ = lean_box(1);
                v___x_5552_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5552_, 0, v___x_5550_);
                lean_ctor_set(v___x_5552_, 1, v___x_5551_);
                v___x_5553_ = l_Lake_instReprVerRange_repr___redArg___closed__6;
                v___x_5554_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5554_, 0, v___x_5552_);
                lean_ctor_set(v___x_5554_, 1, v___x_5553_);
                v___x_5555_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5555_, 0, v___x_5554_);
                lean_ctor_set(v___x_5555_, 1, v___x_5539_);
                v___x_5556_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instReprVerRange_repr___redArg___closed__7),
                    core::ptr::addr_of_mut!(l_Lake_instReprVerRange_repr___redArg___closed__7_once),
                    _init_l_Lake_instReprVerRange_repr___redArg___closed__7,
                );
                v___x_5557_ =
                    l_Array_repr___at___00Lake_instReprVerRange_repr_spec__0(v_clauses_5535_);
                v___x_5558_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5558_, 0, v___x_5556_);
                lean_ctor_set(v___x_5558_, 1, v___x_5557_);
                v___x_5559_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5559_, 0, v___x_5558_);
                lean_ctor_set_uint8(
                    v___x_5559_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5546_,
                );
                v___x_5560_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5560_, 0, v___x_5555_);
                lean_ctor_set(v___x_5560_, 1, v___x_5559_);
                v___x_5561_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_instReprSemVerCore_repr___redArg___closed__16),
                    core::ptr::addr_of_mut!(
                        l_Lake_instReprSemVerCore_repr___redArg___closed__16_once
                    ),
                    _init_l_Lake_instReprSemVerCore_repr___redArg___closed__16,
                );
                v___x_5562_ = l_Lake_instReprSemVerCore_repr___redArg___closed__17;
                v___x_5563_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5563_, 0, v___x_5562_);
                lean_ctor_set(v___x_5563_, 1, v___x_5560_);
                v___x_5564_ = l_Lake_instReprSemVerCore_repr___redArg___closed__18;
                v___x_5565_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_5565_, 0, v___x_5563_);
                lean_ctor_set(v___x_5565_, 1, v___x_5564_);
                v___x_5566_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5566_, 0, v___x_5561_);
                lean_ctor_set(v___x_5566_, 1, v___x_5565_);
                v___x_5567_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5567_, 0, v___x_5566_);
                lean_ctor_set_uint8(
                    v___x_5567_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5546_,
                );
                return v___x_5567_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprVerRange_repr(
    mut v_x_5570_: *mut LeanObject,
    mut v_prec_5571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    v___x_5572_ = l_Lake_instReprVerRange_repr___redArg(v_x_5570_);
    return v___x_5572_;
}
pub unsafe fn l_Lake_instReprVerRange_repr___boxed(
    mut v_x_5573_: *mut LeanObject,
    mut v_prec_5574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5575_: *mut LeanObject = core::ptr::null_mut();
    v_res_5575_ = l_Lake_instReprVerRange_repr(v_x_5573_, v_prec_5574_);
    lean_dec(v_prec_5574_);
    return v_res_5575_;
}
pub unsafe fn l_Lake_VerRange_instToString___lam__0(
    mut v_self_5585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toString_5586_: *mut LeanObject = core::ptr::null_mut();
    v_toString_5586_ = lean_ctor_get(v_self_5585_, 0);
    lean_inc_ref(v_toString_5586_);
    return v_toString_5586_;
}
pub unsafe fn l_Lake_VerRange_instToString___lam__0___boxed(
    mut v_self_5587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5588_: *mut LeanObject = core::ptr::null_mut();
    v_res_5588_ = l_Lake_VerRange_instToString___lam__0(v_self_5587_);
    lean_dec_ref(v_self_5587_);
    return v_res_5588_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(
    mut v_as_5592_: *mut LeanObject,
    mut v_i_5593_: usize,
    mut v_stop_5594_: usize,
    mut v_b_5595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5596_: u8 = 0;
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: usize = 0;
    let mut v___x_5603_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5596_ = lean_usize_dec_eq(v_i_5593_, v_stop_5594_);
                if v___x_5596_ == 0 {
                    v___x_5597_ = lean_array_uget_borrowed(v_as_5592_, v_i_5593_);
                    v___x_5598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___closed__0;
                    v___x_5599_ = lean_string_append(v_b_5595_, v___x_5598_);
                    lean_inc(v___x_5597_);
                    v___x_5600_ = l_Lake_VerComparator_toString(v___x_5597_);
                    v___x_5601_ = lean_string_append(v___x_5599_, v___x_5600_);
                    lean_dec_ref(v___x_5600_);
                    v___x_5602_ = 1usize;
                    v___x_5603_ = lean_usize_add(v_i_5593_, v___x_5602_);
                    v_i_5593_ = v___x_5603_;
                    v_b_5595_ = v___x_5601_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5595_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0___boxed(
    mut v_as_5605_: *mut LeanObject,
    mut v_i_5606_: *mut LeanObject,
    mut v_stop_5607_: *mut LeanObject,
    mut v_b_5608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5609_: usize = 0;
    let mut v_stop_boxed_5610_: usize = 0;
    let mut v_res_5611_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5609_ = lean_unbox_usize(v_i_5606_);
    lean_dec(v_i_5606_);
    v_stop_boxed_5610_ = lean_unbox_usize(v_stop_5607_);
    lean_dec(v_stop_5607_);
    v_res_5611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_as_5605_, v_i_boxed_5609_, v_stop_boxed_5610_, v_b_5608_);
    lean_dec_ref(v_as_5605_);
    return v_res_5611_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(
    mut v_ands_5613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: u8 = 0;
    v___x_5614_ = lean_array_get_size(v_ands_5613_);
    v___x_5615_ = lean_unsigned_to_nat(0);
    v___x_5616_ = lean_nat_dec_eq(v___x_5614_, v___x_5615_);
    if v___x_5616_ == 0 {
        let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5620_: u8 = 0;
        v___x_5617_ = lean_array_fget_borrowed(v_ands_5613_, v___x_5615_);
        lean_inc(v___x_5617_);
        v___x_5618_ = l_Lake_VerComparator_toString(v___x_5617_);
        v___x_5619_ = lean_unsigned_to_nat(1);
        v___x_5620_ = lean_nat_dec_lt(v___x_5619_, v___x_5614_);
        if v___x_5620_ == 0 {
            return v___x_5618_;
        } else {
            let mut v___x_5621_: u8 = 0;
            v___x_5621_ = lean_nat_dec_le(v___x_5614_, v___x_5614_);
            if v___x_5621_ == 0 {
                if v___x_5620_ == 0 {
                    return v___x_5618_;
                } else {
                    let mut v___x_5622_: usize = 0;
                    let mut v___x_5623_: usize = 0;
                    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5622_ = 1usize;
                    v___x_5623_ = lean_usize_of_nat(v___x_5614_);
                    v___x_5624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_5613_, v___x_5622_, v___x_5623_, v___x_5618_);
                    return v___x_5624_;
                }
            } else {
                let mut v___x_5625_: usize = 0;
                let mut v___x_5626_: usize = 0;
                let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
                v___x_5625_ = 1usize;
                v___x_5626_ = lean_usize_of_nat(v___x_5614_);
                v___x_5627_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds_spec__0(v_ands_5613_, v___x_5625_, v___x_5626_, v___x_5618_);
                return v___x_5627_;
            }
        }
    } else {
        let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
        v___x_5628_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___closed__0;
        return v___x_5628_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds___boxed(
    mut v_ands_5629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5630_: *mut LeanObject = core::ptr::null_mut();
    v_res_5630_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v_ands_5629_);
    lean_dec_ref(v_ands_5629_);
    return v_res_5630_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(
    mut v_as_5632_: *mut LeanObject,
    mut v_i_5633_: usize,
    mut v_stop_5634_: usize,
    mut v_b_5635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5636_: u8 = 0;
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: usize = 0;
    let mut v___x_5643_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5636_ = lean_usize_dec_eq(v_i_5633_, v_stop_5634_);
                if v___x_5636_ == 0 {
                    v___x_5637_ = lean_array_uget_borrowed(v_as_5632_, v_i_5633_);
                    v___x_5638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___closed__0;
                    v___x_5639_ = lean_string_append(v_b_5635_, v___x_5638_);
                    v___x_5640_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(
                        v___x_5637_,
                    );
                    v___x_5641_ = lean_string_append(v___x_5639_, v___x_5640_);
                    lean_dec_ref(v___x_5640_);
                    v___x_5642_ = 1usize;
                    v___x_5643_ = lean_usize_add(v_i_5633_, v___x_5642_);
                    v_i_5633_ = v___x_5643_;
                    v_b_5635_ = v___x_5641_;
                    state = 0;
                    continue;
                } else {
                    return v_b_5635_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0___boxed(
    mut v_as_5645_: *mut LeanObject,
    mut v_i_5646_: *mut LeanObject,
    mut v_stop_5647_: *mut LeanObject,
    mut v_b_5648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5649_: usize = 0;
    let mut v_stop_boxed_5650_: usize = 0;
    let mut v_res_5651_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5649_ = lean_unbox_usize(v_i_5646_);
    lean_dec(v_i_5646_);
    v_stop_boxed_5650_ = lean_unbox_usize(v_stop_5647_);
    lean_dec(v_stop_5647_);
    v_res_5651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_as_5645_, v_i_boxed_5649_, v_stop_boxed_5650_, v_b_5648_);
    lean_dec_ref(v_as_5645_);
    return v_res_5651_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(
    mut v_ors_5652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: u8 = 0;
    v___x_5653_ = lean_array_get_size(v_ors_5652_);
    v___x_5654_ = lean_unsigned_to_nat(0);
    v___x_5655_ = lean_nat_dec_eq(v___x_5653_, v___x_5654_);
    if v___x_5655_ == 0 {
        let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5659_: u8 = 0;
        v___x_5656_ = lean_array_fget_borrowed(v_ors_5652_, v___x_5654_);
        v___x_5657_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtAnds(v___x_5656_);
        v___x_5658_ = lean_unsigned_to_nat(1);
        v___x_5659_ = lean_nat_dec_lt(v___x_5658_, v___x_5653_);
        if v___x_5659_ == 0 {
            return v___x_5657_;
        } else {
            let mut v___x_5660_: u8 = 0;
            v___x_5660_ = lean_nat_dec_le(v___x_5653_, v___x_5653_);
            if v___x_5660_ == 0 {
                if v___x_5659_ == 0 {
                    return v___x_5657_;
                } else {
                    let mut v___x_5661_: usize = 0;
                    let mut v___x_5662_: usize = 0;
                    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
                    v___x_5661_ = 1usize;
                    v___x_5662_ = lean_usize_of_nat(v___x_5653_);
                    v___x_5663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_5652_, v___x_5661_, v___x_5662_, v___x_5657_);
                    return v___x_5663_;
                }
            } else {
                let mut v___x_5664_: usize = 0;
                let mut v___x_5665_: usize = 0;
                let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
                v___x_5664_ = 1usize;
                v___x_5665_ = lean_usize_of_nat(v___x_5653_);
                v___x_5666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs_spec__0(v_ors_5652_, v___x_5664_, v___x_5665_, v___x_5657_);
                return v___x_5666_;
            }
        }
    } else {
        let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
        v___x_5667_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
        return v___x_5667_;
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs___boxed(
    mut v_ors_5668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5669_: *mut LeanObject = core::ptr::null_mut();
    v_res_5669_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_ors_5668_);
    lean_dec_ref(v_ors_5668_);
    return v_res_5669_;
}
pub unsafe fn l_Lake_VerRange_ofClauses(mut v_clauses_5670_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    v___x_5671_ = l___private_Lake_Util_Version_0__Lake_VerRange_ofClauses_fmtOrs(v_clauses_5670_);
    v___x_5672_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5672_, 0, v___x_5671_);
    lean_ctor_set(v___x_5672_, 1, v_clauses_5670_);
    return v___x_5672_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_parseM_appendRange(
    mut v_ands_5673_: *mut LeanObject,
    mut v_minVer_5674_: *mut LeanObject,
    mut v_maxVer_5675_: *mut LeanObject,
    mut v_specialDescr_5676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_minVer_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: u8 = 0;
    let mut v___x_5681_: u8 = 0;
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: u8 = 0;
    let mut v___x_5685_: u8 = 0;
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    v_minVer_5677_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_minVer_5677_, 0, v_minVer_5674_);
    lean_ctor_set(v_minVer_5677_, 1, v_specialDescr_5676_);
    v___x_5678_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
    v_maxVer_5679_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_maxVer_5679_, 0, v_maxVer_5675_);
    lean_ctor_set(v_maxVer_5679_, 1, v___x_5678_);
    v___x_5680_ = 3;
    v___x_5681_ = 0;
    v___x_5682_ = lean_alloc_ctor(0, 1, (2) as u32);
    lean_ctor_set(v___x_5682_, 0, v_minVer_5677_);
    lean_ctor_set_uint8(
        v___x_5682_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5680_,
    );
    lean_ctor_set_uint8(
        v___x_5682_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
        v___x_5681_,
    );
    v___x_5683_ = lean_array_push(v_ands_5673_, v___x_5682_);
    v___x_5684_ = 0;
    v___x_5685_ = 1;
    v___x_5686_ = lean_alloc_ctor(0, 1, (2) as u32);
    lean_ctor_set(v___x_5686_, 0, v_maxVer_5679_);
    lean_ctor_set_uint8(
        v___x_5686_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_5684_,
    );
    lean_ctor_set_uint8(
        v___x_5686_,
        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
        v___x_5685_,
    );
    v___x_5687_ = lean_array_push(v___x_5683_, v___x_5686_);
    return v___x_5687_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(
    mut v_s_5690_: *mut LeanObject,
    mut v_ands_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5700_: u8 = 0;
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5706_: u8 = 0;
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: u8 = 0;
    let mut v___x_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: u8 = 0;
    let mut v___x_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: u8 = 0;
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: u8 = 0;
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: u8 = 0;
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: u8 = 0;
    let mut v___x_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: u8 = 0;
    let mut v___x_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: u8 = 0;
    let mut v___x_5837_: u8 = 0;
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: u8 = 0;
    let mut v___x_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5858_: u8 = 0;
    let mut v_a_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5863_: u8 = 0;
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5867_: u8 = 0;
    let mut v_isSharedCheck_5868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5693_ = lean_unsigned_to_nat(0);
                v___x_5694_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0;
                lean_inc(v_a_5692_);
                lean_inc_ref(v_s_5690_);
                v___x_5695_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(
                    v_s_5690_,
                    v___x_5694_,
                    v_a_5692_,
                    v_a_5692_,
                );
                v_a_5696_ = lean_ctor_get(v___x_5695_, 0);
                v_a_5697_ = lean_ctor_get(v___x_5695_, 1);
                v_isSharedCheck_5868_ = (!lean_is_exclusive(v___x_5695_)) as u8;
                if v_isSharedCheck_5868_ == 0 {
                    v___x_5699_ = v___x_5695_;
                    v_isShared_5700_ = v_isSharedCheck_5868_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5697_);
                    lean_inc(v_a_5696_);
                    lean_dec(v___x_5695_);
                    v___x_5699_ = lean_box(0);
                    v_isShared_5700_ = v_isSharedCheck_5868_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5701_ =
                    l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_5690_, v_a_5697_);
                lean_dec_ref(v_s_5690_);
                if lean_obj_tag(v___x_5701_) == 0 {
                    v_a_5702_ = lean_ctor_get(v___x_5701_, 0);
                    v_a_5703_ = lean_ctor_get(v___x_5701_, 1);
                    v_isSharedCheck_5858_ = (!lean_is_exclusive(v___x_5701_)) as u8;
                    if v_isSharedCheck_5858_ == 0 {
                        v___x_5705_ = v___x_5701_;
                        v_isShared_5706_ = v_isSharedCheck_5858_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5703_);
                        lean_inc(v_a_5702_);
                        lean_dec(v___x_5701_);
                        v___x_5705_ = lean_box(0);
                        v_isShared_5706_ = v_isSharedCheck_5858_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5699_);
                    lean_dec(v_a_5696_);
                    lean_dec_ref(v_ands_5691_);
                    v_a_5859_ = lean_ctor_get(v___x_5701_, 0);
                    v_a_5860_ = lean_ctor_get(v___x_5701_, 1);
                    v_isSharedCheck_5867_ = (!lean_is_exclusive(v___x_5701_)) as u8;
                    if v_isSharedCheck_5867_ == 0 {
                        v___x_5862_ = v___x_5701_;
                        v_isShared_5863_ = v_isSharedCheck_5867_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_5860_);
                        lean_inc(v_a_5859_);
                        lean_dec(v___x_5701_);
                        v___x_5862_ = lean_box(0);
                        v_isShared_5863_ = v_isSharedCheck_5867_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5707_ = lean_array_get_size(v_a_5696_);
                v___x_5708_ = lean_unsigned_to_nat(1);
                v___x_5709_ = lean_nat_dec_eq(v___x_5707_, v___x_5708_);
                if v___x_5709_ == 0 {
                    v___x_5710_ = lean_unsigned_to_nat(2);
                    v___x_5711_ = lean_nat_dec_eq(v___x_5707_, v___x_5710_);
                    if v___x_5711_ == 0 {
                        v___x_5712_ = lean_unsigned_to_nat(3);
                        v___x_5713_ = lean_nat_dec_eq(v___x_5707_, v___x_5712_);
                        if v___x_5713_ == 0 {
                            lean_dec(v_a_5702_);
                            lean_del_object(v___x_5699_);
                            lean_dec(v_a_5696_);
                            lean_dec_ref(v_ands_5691_);
                            v___x_5714_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__0;
                            v___x_5715_ = l_Nat_reprFast(v___x_5707_);
                            v___x_5716_ = lean_string_append(v___x_5714_, v___x_5715_);
                            lean_dec_ref(v___x_5715_);
                            v___x_5717_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1;
                            v___x_5718_ = lean_string_append(v___x_5716_, v___x_5717_);
                            if v_isShared_5706_ == 0 {
                                lean_ctor_set_tag(v___x_5705_, 1);
                                lean_ctor_set(v___x_5705_, 0, v___x_5718_);
                                v___x_5720_ = v___x_5705_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5718_);
                                lean_ctor_set(v_reuseFailAlloc_5721_, 1, v_a_5703_);
                                v___x_5720_ = v_reuseFailAlloc_5721_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_5722_ = lean_array_fget_borrowed(v_a_5696_, v___x_5693_);
                            v___x_5723_ = l_String_Slice_toNat_x3f(v___x_5722_);
                            if lean_obj_tag(v___x_5723_) == 1 {
                                v_val_5724_ = lean_ctor_get(v___x_5723_, 0);
                                lean_inc(v_val_5724_);
                                lean_dec_ref_known(v___x_5723_, 1);
                                v___x_5725_ = lean_array_fget_borrowed(v_a_5696_, v___x_5708_);
                                v___x_5726_ = l_String_Slice_toNat_x3f(v___x_5725_);
                                if lean_obj_tag(v___x_5726_) == 1 {
                                    v_val_5727_ = lean_ctor_get(v___x_5726_, 0);
                                    lean_inc(v_val_5727_);
                                    lean_dec_ref_known(v___x_5726_, 1);
                                    v___x_5728_ = lean_array_fget(v_a_5696_, v___x_5710_);
                                    lean_dec(v_a_5696_);
                                    v___x_5729_ = l_String_Slice_toNat_x3f(v___x_5728_);
                                    if lean_obj_tag(v___x_5729_) == 1 {
                                        lean_dec(v___x_5728_);
                                        v_val_5730_ = lean_ctor_get(v___x_5729_, 0);
                                        lean_inc(v_val_5730_);
                                        lean_dec_ref_known(v___x_5729_, 1);
                                        lean_inc(v_val_5727_);
                                        lean_inc(v_val_5724_);
                                        v___x_5731_ = lean_alloc_ctor(0, 3, (0) as u32);
                                        lean_ctor_set(v___x_5731_, 0, v_val_5724_);
                                        lean_ctor_set(v___x_5731_, 1, v_val_5727_);
                                        lean_ctor_set(v___x_5731_, 2, v_val_5730_);
                                        v___x_5732_ = lean_nat_add(v_val_5727_, v___x_5708_);
                                        lean_dec(v_val_5727_);
                                        v___x_5733_ = lean_alloc_ctor(0, 3, (0) as u32);
                                        lean_ctor_set(v___x_5733_, 0, v_val_5724_);
                                        lean_ctor_set(v___x_5733_, 1, v___x_5732_);
                                        lean_ctor_set(v___x_5733_, 2, v___x_5693_);
                                        if v_isShared_5700_ == 0 {
                                            lean_ctor_set(v___x_5699_, 1, v_a_5702_);
                                            lean_ctor_set(v___x_5699_, 0, v___x_5731_);
                                            v_minVer_5735_ = v___x_5699_;
                                            state = 4;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_5747_ =
                                                lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_5747_, 0, v___x_5731_);
                                            lean_ctor_set(v_reuseFailAlloc_5747_, 1, v_a_5702_);
                                            v_minVer_5735_ = v_reuseFailAlloc_5747_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_5729_);
                                        lean_dec(v_val_5727_);
                                        lean_dec(v_val_5724_);
                                        lean_dec(v_a_5702_);
                                        lean_del_object(v___x_5699_);
                                        lean_dec_ref(v_ands_5691_);
                                        v_str_5748_ = lean_ctor_get(v___x_5728_, 0);
                                        lean_inc_ref(v_str_5748_);
                                        v_startInclusive_5749_ = lean_ctor_get(v___x_5728_, 1);
                                        lean_inc(v_startInclusive_5749_);
                                        v_endExclusive_5750_ = lean_ctor_get(v___x_5728_, 2);
                                        lean_inc(v_endExclusive_5750_);
                                        lean_dec(v___x_5728_);
                                        v___x_5751_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3;
                                        v___x_5752_ = lean_string_utf8_extract(
                                            v_str_5748_,
                                            v_startInclusive_5749_,
                                            v_endExclusive_5750_,
                                        );
                                        lean_dec(v_endExclusive_5750_);
                                        lean_dec(v_startInclusive_5749_);
                                        lean_dec_ref(v_str_5748_);
                                        v___x_5753_ = lean_string_append(v___x_5751_, v___x_5752_);
                                        lean_dec_ref(v___x_5752_);
                                        v___x_5754_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                        v___x_5755_ = lean_string_append(v___x_5753_, v___x_5754_);
                                        if v_isShared_5706_ == 0 {
                                            lean_ctor_set_tag(v___x_5705_, 1);
                                            lean_ctor_set(v___x_5705_, 0, v___x_5755_);
                                            v___x_5757_ = v___x_5705_;
                                            state = 6;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_5758_ =
                                                lean_alloc_ctor(1, 2, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_5758_, 0, v___x_5755_);
                                            lean_ctor_set(v_reuseFailAlloc_5758_, 1, v_a_5703_);
                                            v___x_5757_ = v_reuseFailAlloc_5758_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_inc(v___x_5725_);
                                    lean_dec(v___x_5726_);
                                    lean_dec(v_val_5724_);
                                    lean_dec(v_a_5702_);
                                    lean_del_object(v___x_5699_);
                                    lean_dec(v_a_5696_);
                                    lean_dec_ref(v_ands_5691_);
                                    v_str_5759_ = lean_ctor_get(v___x_5725_, 0);
                                    lean_inc_ref(v_str_5759_);
                                    v_startInclusive_5760_ = lean_ctor_get(v___x_5725_, 1);
                                    lean_inc(v_startInclusive_5760_);
                                    v_endExclusive_5761_ = lean_ctor_get(v___x_5725_, 2);
                                    lean_inc(v_endExclusive_5761_);
                                    lean_dec(v___x_5725_);
                                    v___x_5762_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4;
                                    v___x_5763_ = lean_string_utf8_extract(
                                        v_str_5759_,
                                        v_startInclusive_5760_,
                                        v_endExclusive_5761_,
                                    );
                                    lean_dec(v_endExclusive_5761_);
                                    lean_dec(v_startInclusive_5760_);
                                    lean_dec_ref(v_str_5759_);
                                    v___x_5764_ = lean_string_append(v___x_5762_, v___x_5763_);
                                    lean_dec_ref(v___x_5763_);
                                    v___x_5765_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                    v___x_5766_ = lean_string_append(v___x_5764_, v___x_5765_);
                                    if v_isShared_5706_ == 0 {
                                        lean_ctor_set_tag(v___x_5705_, 1);
                                        lean_ctor_set(v___x_5705_, 0, v___x_5766_);
                                        v___x_5768_ = v___x_5705_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5769_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5769_, 0, v___x_5766_);
                                        lean_ctor_set(v_reuseFailAlloc_5769_, 1, v_a_5703_);
                                        v___x_5768_ = v_reuseFailAlloc_5769_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v___x_5722_);
                                lean_dec(v___x_5723_);
                                lean_dec(v_a_5702_);
                                lean_del_object(v___x_5699_);
                                lean_dec(v_a_5696_);
                                lean_dec_ref(v_ands_5691_);
                                v_str_5770_ = lean_ctor_get(v___x_5722_, 0);
                                lean_inc_ref(v_str_5770_);
                                v_startInclusive_5771_ = lean_ctor_get(v___x_5722_, 1);
                                lean_inc(v_startInclusive_5771_);
                                v_endExclusive_5772_ = lean_ctor_get(v___x_5722_, 2);
                                lean_inc(v_endExclusive_5772_);
                                lean_dec(v___x_5722_);
                                v___x_5773_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5;
                                v___x_5774_ = lean_string_utf8_extract(
                                    v_str_5770_,
                                    v_startInclusive_5771_,
                                    v_endExclusive_5772_,
                                );
                                lean_dec(v_endExclusive_5772_);
                                lean_dec(v_startInclusive_5771_);
                                lean_dec_ref(v_str_5770_);
                                v___x_5775_ = lean_string_append(v___x_5773_, v___x_5774_);
                                lean_dec_ref(v___x_5774_);
                                v___x_5776_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                v___x_5777_ = lean_string_append(v___x_5775_, v___x_5776_);
                                if v_isShared_5706_ == 0 {
                                    lean_ctor_set_tag(v___x_5705_, 1);
                                    lean_ctor_set(v___x_5705_, 0, v___x_5777_);
                                    v___x_5779_ = v___x_5705_;
                                    state = 8;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5780_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5777_);
                                    lean_ctor_set(v_reuseFailAlloc_5780_, 1, v_a_5703_);
                                    v___x_5779_ = v_reuseFailAlloc_5780_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_5781_ = lean_array_fget_borrowed(v_a_5696_, v___x_5693_);
                        v___x_5782_ = l_String_Slice_toNat_x3f(v___x_5781_);
                        if lean_obj_tag(v___x_5782_) == 1 {
                            v_val_5783_ = lean_ctor_get(v___x_5782_, 0);
                            lean_inc(v_val_5783_);
                            lean_dec_ref_known(v___x_5782_, 1);
                            v___x_5784_ = lean_array_fget(v_a_5696_, v___x_5708_);
                            lean_dec(v_a_5696_);
                            v___x_5785_ = l_String_Slice_toNat_x3f(v___x_5784_);
                            if lean_obj_tag(v___x_5785_) == 1 {
                                lean_dec(v___x_5784_);
                                v_val_5786_ = lean_ctor_get(v___x_5785_, 0);
                                lean_inc_n(v_val_5786_, 2);
                                lean_dec_ref_known(v___x_5785_, 1);
                                lean_inc(v_val_5783_);
                                v___x_5787_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_5787_, 0, v_val_5783_);
                                lean_ctor_set(v___x_5787_, 1, v_val_5786_);
                                lean_ctor_set(v___x_5787_, 2, v___x_5693_);
                                v___x_5788_ = lean_nat_add(v_val_5786_, v___x_5708_);
                                lean_dec(v_val_5786_);
                                v___x_5789_ = lean_alloc_ctor(0, 3, (0) as u32);
                                lean_ctor_set(v___x_5789_, 0, v_val_5783_);
                                lean_ctor_set(v___x_5789_, 1, v___x_5788_);
                                lean_ctor_set(v___x_5789_, 2, v___x_5693_);
                                if v_isShared_5700_ == 0 {
                                    lean_ctor_set(v___x_5699_, 1, v_a_5702_);
                                    lean_ctor_set(v___x_5699_, 0, v___x_5787_);
                                    v_minVer_5791_ = v___x_5699_;
                                    state = 9;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5787_);
                                    lean_ctor_set(v_reuseFailAlloc_5803_, 1, v_a_5702_);
                                    v_minVer_5791_ = v_reuseFailAlloc_5803_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_5785_);
                                lean_dec(v_val_5783_);
                                lean_dec(v_a_5702_);
                                lean_del_object(v___x_5699_);
                                lean_dec_ref(v_ands_5691_);
                                v_str_5804_ = lean_ctor_get(v___x_5784_, 0);
                                lean_inc_ref(v_str_5804_);
                                v_startInclusive_5805_ = lean_ctor_get(v___x_5784_, 1);
                                lean_inc(v_startInclusive_5805_);
                                v_endExclusive_5806_ = lean_ctor_get(v___x_5784_, 2);
                                lean_inc(v_endExclusive_5806_);
                                lean_dec(v___x_5784_);
                                v___x_5807_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4;
                                v___x_5808_ = lean_string_utf8_extract(
                                    v_str_5804_,
                                    v_startInclusive_5805_,
                                    v_endExclusive_5806_,
                                );
                                lean_dec(v_endExclusive_5806_);
                                lean_dec(v_startInclusive_5805_);
                                lean_dec_ref(v_str_5804_);
                                v___x_5809_ = lean_string_append(v___x_5807_, v___x_5808_);
                                lean_dec_ref(v___x_5808_);
                                v___x_5810_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                v___x_5811_ = lean_string_append(v___x_5809_, v___x_5810_);
                                if v_isShared_5706_ == 0 {
                                    lean_ctor_set_tag(v___x_5705_, 1);
                                    lean_ctor_set(v___x_5705_, 0, v___x_5811_);
                                    v___x_5813_ = v___x_5705_;
                                    state = 11;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5814_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_5814_, 0, v___x_5811_);
                                    lean_ctor_set(v_reuseFailAlloc_5814_, 1, v_a_5703_);
                                    v___x_5813_ = v_reuseFailAlloc_5814_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v___x_5781_);
                            lean_dec(v___x_5782_);
                            lean_dec(v_a_5702_);
                            lean_del_object(v___x_5699_);
                            lean_dec(v_a_5696_);
                            lean_dec_ref(v_ands_5691_);
                            v_str_5815_ = lean_ctor_get(v___x_5781_, 0);
                            lean_inc_ref(v_str_5815_);
                            v_startInclusive_5816_ = lean_ctor_get(v___x_5781_, 1);
                            lean_inc(v_startInclusive_5816_);
                            v_endExclusive_5817_ = lean_ctor_get(v___x_5781_, 2);
                            lean_inc(v_endExclusive_5817_);
                            lean_dec(v___x_5781_);
                            v___x_5818_ =
                                l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5;
                            v___x_5819_ = lean_string_utf8_extract(
                                v_str_5815_,
                                v_startInclusive_5816_,
                                v_endExclusive_5817_,
                            );
                            lean_dec(v_endExclusive_5817_);
                            lean_dec(v_startInclusive_5816_);
                            lean_dec_ref(v_str_5815_);
                            v___x_5820_ = lean_string_append(v___x_5818_, v___x_5819_);
                            lean_dec_ref(v___x_5819_);
                            v___x_5821_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                            v___x_5822_ = lean_string_append(v___x_5820_, v___x_5821_);
                            if v_isShared_5706_ == 0 {
                                lean_ctor_set_tag(v___x_5705_, 1);
                                lean_ctor_set(v___x_5705_, 0, v___x_5822_);
                                v___x_5824_ = v___x_5705_;
                                state = 12;
                                continue;
                            } else {
                                v_reuseFailAlloc_5825_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5825_, 0, v___x_5822_);
                                lean_ctor_set(v_reuseFailAlloc_5825_, 1, v_a_5703_);
                                v___x_5824_ = v_reuseFailAlloc_5825_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5826_ = lean_array_fget(v_a_5696_, v___x_5693_);
                    lean_dec(v_a_5696_);
                    v___x_5827_ = l_String_Slice_toNat_x3f(v___x_5826_);
                    if lean_obj_tag(v___x_5827_) == 1 {
                        lean_dec(v___x_5826_);
                        v_val_5828_ = lean_ctor_get(v___x_5827_, 0);
                        lean_inc_n(v_val_5828_, 2);
                        lean_dec_ref_known(v___x_5827_, 1);
                        v___x_5829_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_5829_, 0, v_val_5828_);
                        lean_ctor_set(v___x_5829_, 1, v___x_5693_);
                        lean_ctor_set(v___x_5829_, 2, v___x_5693_);
                        v___x_5830_ = lean_nat_add(v_val_5828_, v___x_5708_);
                        lean_dec(v_val_5828_);
                        v___x_5831_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_5831_, 0, v___x_5830_);
                        lean_ctor_set(v___x_5831_, 1, v___x_5693_);
                        lean_ctor_set(v___x_5831_, 2, v___x_5693_);
                        if v_isShared_5700_ == 0 {
                            lean_ctor_set(v___x_5699_, 1, v_a_5702_);
                            lean_ctor_set(v___x_5699_, 0, v___x_5829_);
                            v_minVer_5833_ = v___x_5699_;
                            state = 13;
                            continue;
                        } else {
                            v_reuseFailAlloc_5846_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5846_, 0, v___x_5829_);
                            lean_ctor_set(v_reuseFailAlloc_5846_, 1, v_a_5702_);
                            v_minVer_5833_ = v_reuseFailAlloc_5846_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_5827_);
                        lean_dec(v_a_5702_);
                        lean_del_object(v___x_5699_);
                        lean_dec_ref(v_ands_5691_);
                        v_str_5847_ = lean_ctor_get(v___x_5826_, 0);
                        lean_inc_ref(v_str_5847_);
                        v_startInclusive_5848_ = lean_ctor_get(v___x_5826_, 1);
                        lean_inc(v_startInclusive_5848_);
                        v_endExclusive_5849_ = lean_ctor_get(v___x_5826_, 2);
                        lean_inc(v_endExclusive_5849_);
                        lean_dec(v___x_5826_);
                        v___x_5850_ =
                            l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5;
                        v___x_5851_ = lean_string_utf8_extract(
                            v_str_5847_,
                            v_startInclusive_5848_,
                            v_endExclusive_5849_,
                        );
                        lean_dec(v_endExclusive_5849_);
                        lean_dec(v_startInclusive_5848_);
                        lean_dec_ref(v_str_5847_);
                        v___x_5852_ = lean_string_append(v___x_5850_, v___x_5851_);
                        lean_dec_ref(v___x_5851_);
                        v___x_5853_ =
                            l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                        v___x_5854_ = lean_string_append(v___x_5852_, v___x_5853_);
                        if v_isShared_5706_ == 0 {
                            lean_ctor_set_tag(v___x_5705_, 1);
                            lean_ctor_set(v___x_5705_, 0, v___x_5854_);
                            v___x_5856_ = v___x_5705_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_5857_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5857_, 0, v___x_5854_);
                            lean_ctor_set(v_reuseFailAlloc_5857_, 1, v_a_5703_);
                            v___x_5856_ = v_reuseFailAlloc_5857_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_5720_;
            }
            4 => {
                v___x_5736_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                v_maxVer_5737_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_maxVer_5737_, 0, v___x_5733_);
                lean_ctor_set(v_maxVer_5737_, 1, v___x_5736_);
                v___x_5738_ = 3;
                v___x_5739_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_5739_, 0, v_minVer_5735_);
                lean_ctor_set_uint8(
                    v___x_5739_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5738_,
                );
                lean_ctor_set_uint8(
                    v___x_5739_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_5711_,
                );
                v___x_5740_ = lean_array_push(v_ands_5691_, v___x_5739_);
                v___x_5741_ = 0;
                v___x_5742_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_5742_, 0, v_maxVer_5737_);
                lean_ctor_set_uint8(
                    v___x_5742_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5741_,
                );
                lean_ctor_set_uint8(
                    v___x_5742_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_5713_,
                );
                v___x_5743_ = lean_array_push(v___x_5740_, v___x_5742_);
                if v_isShared_5706_ == 0 {
                    lean_ctor_set(v___x_5705_, 0, v___x_5743_);
                    v___x_5745_ = v___x_5705_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5746_, 0, v___x_5743_);
                    lean_ctor_set(v_reuseFailAlloc_5746_, 1, v_a_5703_);
                    v___x_5745_ = v_reuseFailAlloc_5746_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5745_;
            }
            6 => {
                return v___x_5757_;
            }
            7 => {
                return v___x_5768_;
            }
            8 => {
                return v___x_5779_;
            }
            9 => {
                v___x_5792_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                v_maxVer_5793_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_maxVer_5793_, 0, v___x_5789_);
                lean_ctor_set(v_maxVer_5793_, 1, v___x_5792_);
                v___x_5794_ = 3;
                v___x_5795_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_5795_, 0, v_minVer_5791_);
                lean_ctor_set_uint8(
                    v___x_5795_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5794_,
                );
                lean_ctor_set_uint8(
                    v___x_5795_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_5709_,
                );
                v___x_5796_ = lean_array_push(v_ands_5691_, v___x_5795_);
                v___x_5797_ = 0;
                v___x_5798_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_5798_, 0, v_maxVer_5793_);
                lean_ctor_set_uint8(
                    v___x_5798_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5797_,
                );
                lean_ctor_set_uint8(
                    v___x_5798_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_5711_,
                );
                v___x_5799_ = lean_array_push(v___x_5796_, v___x_5798_);
                if v_isShared_5706_ == 0 {
                    lean_ctor_set(v___x_5705_, 0, v___x_5799_);
                    v___x_5801_ = v___x_5705_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5802_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5802_, 0, v___x_5799_);
                    lean_ctor_set(v_reuseFailAlloc_5802_, 1, v_a_5703_);
                    v___x_5801_ = v_reuseFailAlloc_5802_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5801_;
            }
            11 => {
                return v___x_5813_;
            }
            12 => {
                return v___x_5824_;
            }
            13 => {
                v___x_5834_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                v_maxVer_5835_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v_maxVer_5835_, 0, v___x_5831_);
                lean_ctor_set(v_maxVer_5835_, 1, v___x_5834_);
                v___x_5836_ = 3;
                v___x_5837_ = 0;
                v___x_5838_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_5838_, 0, v_minVer_5833_);
                lean_ctor_set_uint8(
                    v___x_5838_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5836_,
                );
                lean_ctor_set_uint8(
                    v___x_5838_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_5837_,
                );
                v___x_5839_ = lean_array_push(v_ands_5691_, v___x_5838_);
                v___x_5840_ = 0;
                v___x_5841_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_5841_, 0, v_maxVer_5835_);
                lean_ctor_set_uint8(
                    v___x_5841_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5840_,
                );
                lean_ctor_set_uint8(
                    v___x_5841_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_5709_,
                );
                v___x_5842_ = lean_array_push(v___x_5839_, v___x_5841_);
                if v_isShared_5706_ == 0 {
                    lean_ctor_set(v___x_5705_, 0, v___x_5842_);
                    v___x_5844_ = v___x_5705_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5845_, 0, v___x_5842_);
                    lean_ctor_set(v_reuseFailAlloc_5845_, 1, v_a_5703_);
                    v___x_5844_ = v_reuseFailAlloc_5845_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5844_;
            }
            15 => {
                return v___x_5856_;
            }
            16 => {
                if v_isShared_5863_ == 0 {
                    v___x_5865_ = v___x_5862_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5866_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5859_);
                    lean_ctor_set(v_reuseFailAlloc_5866_, 1, v_a_5860_);
                    v___x_5865_ = v_reuseFailAlloc_5866_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(
    mut v_s_5871_: *mut LeanObject,
    mut v_ands_5872_: *mut LeanObject,
    mut v_a_5873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5881_: u8 = 0;
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v___x_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: u8 = 0;
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: u8 = 0;
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: u8 = 0;
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5913_: u8 = 0;
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: u8 = 0;
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: u8 = 0;
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: u8 = 0;
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: u8 = 0;
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: u8 = 0;
    let mut v___x_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: u8 = 0;
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: u8 = 0;
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: u8 = 0;
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: u8 = 0;
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: u8 = 0;
    let mut v_str_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6007_: u8 = 0;
    let mut v___x_6008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_6011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: u8 = 0;
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: u8 = 0;
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_6028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: u8 = 0;
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: u8 = 0;
    let mut v___x_6033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: u8 = 0;
    let mut v___x_6070_: u8 = 0;
    let mut v___x_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: u8 = 0;
    let mut v___x_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6090_: u8 = 0;
    let mut v_a_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v_isSharedCheck_6100_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5874_ = lean_unsigned_to_nat(0);
                v___x_5875_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0;
                lean_inc(v_a_5873_);
                lean_inc_ref(v_s_5871_);
                v___x_5876_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(
                    v_s_5871_,
                    v___x_5875_,
                    v_a_5873_,
                    v_a_5873_,
                );
                v_a_5877_ = lean_ctor_get(v___x_5876_, 0);
                v_a_5878_ = lean_ctor_get(v___x_5876_, 1);
                v_isSharedCheck_6100_ = (!lean_is_exclusive(v___x_5876_)) as u8;
                if v_isSharedCheck_6100_ == 0 {
                    v___x_5880_ = v___x_5876_;
                    v_isShared_5881_ = v_isSharedCheck_6100_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5878_);
                    lean_inc(v_a_5877_);
                    lean_dec(v___x_5876_);
                    v___x_5880_ = lean_box(0);
                    v_isShared_5881_ = v_isSharedCheck_6100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5882_ =
                    l___private_Lake_Util_Version_0__Lake_parseSpecialDescr(v_s_5871_, v_a_5878_);
                lean_dec_ref(v_s_5871_);
                if lean_obj_tag(v___x_5882_) == 0 {
                    v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
                    v_a_5884_ = lean_ctor_get(v___x_5882_, 1);
                    v_isSharedCheck_6090_ = (!lean_is_exclusive(v___x_5882_)) as u8;
                    if v_isSharedCheck_6090_ == 0 {
                        v___x_5886_ = v___x_5882_;
                        v_isShared_5887_ = v_isSharedCheck_6090_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5884_);
                        lean_inc(v_a_5883_);
                        lean_dec(v___x_5882_);
                        v___x_5886_ = lean_box(0);
                        v_isShared_5887_ = v_isSharedCheck_6090_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5880_);
                    lean_dec(v_a_5877_);
                    lean_dec_ref(v_ands_5872_);
                    v_a_6091_ = lean_ctor_get(v___x_5882_, 0);
                    v_a_6092_ = lean_ctor_get(v___x_5882_, 1);
                    v_isSharedCheck_6099_ = (!lean_is_exclusive(v___x_5882_)) as u8;
                    if v_isSharedCheck_6099_ == 0 {
                        v___x_6094_ = v___x_5882_;
                        v_isShared_6095_ = v_isSharedCheck_6099_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_6092_);
                        lean_inc(v_a_6091_);
                        lean_dec(v___x_5882_);
                        v___x_6094_ = lean_box(0);
                        v_isShared_6095_ = v_isSharedCheck_6099_;
                        state = 18;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5888_ = lean_array_get_size(v_a_5877_);
                v___x_5889_ = lean_unsigned_to_nat(1);
                v___x_5890_ = lean_nat_dec_eq(v___x_5888_, v___x_5889_);
                if v___x_5890_ == 0 {
                    v___x_5891_ = lean_unsigned_to_nat(2);
                    v___x_5892_ = lean_nat_dec_eq(v___x_5888_, v___x_5891_);
                    if v___x_5892_ == 0 {
                        v___x_5893_ = lean_unsigned_to_nat(3);
                        v___x_5894_ = lean_nat_dec_eq(v___x_5888_, v___x_5893_);
                        if v___x_5894_ == 0 {
                            lean_dec(v_a_5883_);
                            lean_del_object(v___x_5880_);
                            lean_dec(v_a_5877_);
                            lean_dec_ref(v_ands_5872_);
                            v___x_5895_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__0;
                            v___x_5896_ = l_Nat_reprFast(v___x_5888_);
                            v___x_5897_ = lean_string_append(v___x_5895_, v___x_5896_);
                            lean_dec_ref(v___x_5896_);
                            v___x_5898_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1;
                            v___x_5899_ = lean_string_append(v___x_5897_, v___x_5898_);
                            if v_isShared_5887_ == 0 {
                                lean_ctor_set_tag(v___x_5886_, 1);
                                lean_ctor_set(v___x_5886_, 0, v___x_5899_);
                                v___x_5901_ = v___x_5886_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_5902_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5902_, 0, v___x_5899_);
                                lean_ctor_set(v_reuseFailAlloc_5902_, 1, v_a_5884_);
                                v___x_5901_ = v_reuseFailAlloc_5902_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v___x_5903_ = lean_array_fget_borrowed(v_a_5877_, v___x_5874_);
                            v___x_5904_ = l_String_Slice_toNat_x3f(v___x_5903_);
                            if lean_obj_tag(v___x_5904_) == 1 {
                                v_val_5905_ = lean_ctor_get(v___x_5904_, 0);
                                lean_inc(v_val_5905_);
                                lean_dec_ref_known(v___x_5904_, 1);
                                v___x_5906_ = lean_array_fget_borrowed(v_a_5877_, v___x_5889_);
                                v___x_5907_ = l_String_Slice_toNat_x3f(v___x_5906_);
                                if lean_obj_tag(v___x_5907_) == 1 {
                                    v_val_5908_ = lean_ctor_get(v___x_5907_, 0);
                                    lean_inc(v_val_5908_);
                                    lean_dec_ref_known(v___x_5907_, 1);
                                    v___x_5909_ = lean_array_fget(v_a_5877_, v___x_5891_);
                                    lean_dec(v_a_5877_);
                                    v___x_5910_ = l_String_Slice_toNat_x3f(v___x_5909_);
                                    if lean_obj_tag(v___x_5910_) == 1 {
                                        lean_dec(v___x_5909_);
                                        v_val_5911_ = lean_ctor_get(v___x_5910_, 0);
                                        lean_inc(v_val_5911_);
                                        lean_dec_ref_known(v___x_5910_, 1);
                                        v___x_5933_ = lean_nat_dec_eq(v_val_5905_, v___x_5874_);
                                        if v___x_5933_ == 0 {
                                            lean_del_object(v___x_5886_);
                                            lean_inc(v_val_5905_);
                                            v___x_5934_ = lean_alloc_ctor(0, 3, (0) as u32);
                                            lean_ctor_set(v___x_5934_, 0, v_val_5905_);
                                            lean_ctor_set(v___x_5934_, 1, v_val_5908_);
                                            lean_ctor_set(v___x_5934_, 2, v_val_5911_);
                                            v___x_5935_ = lean_nat_add(v_val_5905_, v___x_5889_);
                                            lean_dec(v_val_5905_);
                                            v___x_5936_ = lean_alloc_ctor(0, 3, (0) as u32);
                                            lean_ctor_set(v___x_5936_, 0, v___x_5935_);
                                            lean_ctor_set(v___x_5936_, 1, v___x_5874_);
                                            lean_ctor_set(v___x_5936_, 2, v___x_5874_);
                                            v_minVer_5937_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_minVer_5937_, 0, v___x_5934_);
                                            lean_ctor_set(v_minVer_5937_, 1, v_a_5883_);
                                            v___x_5938_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                                            v_maxVer_5939_ = lean_alloc_ctor(0, 2, (0) as u32);
                                            lean_ctor_set(v_maxVer_5939_, 0, v___x_5936_);
                                            lean_ctor_set(v_maxVer_5939_, 1, v___x_5938_);
                                            v___x_5940_ = 3;
                                            v___x_5941_ = lean_alloc_ctor(0, 1, (2) as u32);
                                            lean_ctor_set(v___x_5941_, 0, v_minVer_5937_);
                                            lean_ctor_set_uint8(
                                                v___x_5941_,
                                                (core::mem::size_of::<*mut LeanObject>() * 1)
                                                    as u32,
                                                v___x_5940_,
                                            );
                                            lean_ctor_set_uint8(
                                                v___x_5941_,
                                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1)
                                                    as u32,
                                                v___x_5933_,
                                            );
                                            v___x_5942_ =
                                                lean_array_push(v_ands_5872_, v___x_5941_);
                                            v___x_5943_ = 0;
                                            v___x_5944_ = lean_alloc_ctor(0, 1, (2) as u32);
                                            lean_ctor_set(v___x_5944_, 0, v_maxVer_5939_);
                                            lean_ctor_set_uint8(
                                                v___x_5944_,
                                                (core::mem::size_of::<*mut LeanObject>() * 1)
                                                    as u32,
                                                v___x_5943_,
                                            );
                                            lean_ctor_set_uint8(
                                                v___x_5944_,
                                                (core::mem::size_of::<*mut LeanObject>() * 1 + 1)
                                                    as u32,
                                                v___x_5894_,
                                            );
                                            v___x_5945_ = lean_array_push(v___x_5942_, v___x_5944_);
                                            if v_isShared_5881_ == 0 {
                                                lean_ctor_set(v___x_5880_, 1, v_a_5884_);
                                                lean_ctor_set(v___x_5880_, 0, v___x_5945_);
                                                v___x_5947_ = v___x_5880_;
                                                state = 7;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_5948_ =
                                                    lean_alloc_ctor(0, 2, (0) as u32);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_5948_,
                                                    0,
                                                    v___x_5945_,
                                                );
                                                lean_ctor_set(v_reuseFailAlloc_5948_, 1, v_a_5884_);
                                                v___x_5947_ = v_reuseFailAlloc_5948_;
                                                state = 7;
                                                continue;
                                            }
                                        } else {
                                            v___x_5949_ = lean_nat_dec_eq(v_val_5908_, v___x_5874_);
                                            if v___x_5949_ == 0 {
                                                lean_del_object(v___x_5886_);
                                                lean_inc(v_val_5908_);
                                                lean_inc(v_val_5905_);
                                                v___x_5950_ = lean_alloc_ctor(0, 3, (0) as u32);
                                                lean_ctor_set(v___x_5950_, 0, v_val_5905_);
                                                lean_ctor_set(v___x_5950_, 1, v_val_5908_);
                                                lean_ctor_set(v___x_5950_, 2, v_val_5911_);
                                                v___x_5951_ =
                                                    lean_nat_add(v_val_5908_, v___x_5889_);
                                                lean_dec(v_val_5908_);
                                                v___x_5952_ = lean_alloc_ctor(0, 3, (0) as u32);
                                                lean_ctor_set(v___x_5952_, 0, v_val_5905_);
                                                lean_ctor_set(v___x_5952_, 1, v___x_5951_);
                                                lean_ctor_set(v___x_5952_, 2, v___x_5874_);
                                                v_minVer_5953_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                lean_ctor_set(v_minVer_5953_, 0, v___x_5950_);
                                                lean_ctor_set(v_minVer_5953_, 1, v_a_5883_);
                                                v___x_5954_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                                                v_maxVer_5955_ = lean_alloc_ctor(0, 2, (0) as u32);
                                                lean_ctor_set(v_maxVer_5955_, 0, v___x_5952_);
                                                lean_ctor_set(v_maxVer_5955_, 1, v___x_5954_);
                                                v___x_5956_ = 3;
                                                v___x_5957_ = lean_alloc_ctor(0, 1, (2) as u32);
                                                lean_ctor_set(v___x_5957_, 0, v_minVer_5953_);
                                                lean_ctor_set_uint8(
                                                    v___x_5957_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 1)
                                                        as u32,
                                                    v___x_5956_,
                                                );
                                                lean_ctor_set_uint8(
                                                    v___x_5957_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 1
                                                        + 1)
                                                        as u32,
                                                    v___x_5949_,
                                                );
                                                v___x_5958_ =
                                                    lean_array_push(v_ands_5872_, v___x_5957_);
                                                v___x_5959_ = 0;
                                                v___x_5960_ = lean_alloc_ctor(0, 1, (2) as u32);
                                                lean_ctor_set(v___x_5960_, 0, v_maxVer_5955_);
                                                lean_ctor_set_uint8(
                                                    v___x_5960_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 1)
                                                        as u32,
                                                    v___x_5959_,
                                                );
                                                lean_ctor_set_uint8(
                                                    v___x_5960_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 1
                                                        + 1)
                                                        as u32,
                                                    v___x_5933_,
                                                );
                                                v___x_5961_ =
                                                    lean_array_push(v___x_5958_, v___x_5960_);
                                                if v_isShared_5881_ == 0 {
                                                    lean_ctor_set(v___x_5880_, 1, v_a_5884_);
                                                    lean_ctor_set(v___x_5880_, 0, v___x_5961_);
                                                    v___x_5963_ = v___x_5880_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_5964_ =
                                                        lean_alloc_ctor(0, 2, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_5964_,
                                                        0,
                                                        v___x_5961_,
                                                    );
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_5964_,
                                                        1,
                                                        v_a_5884_,
                                                    );
                                                    v___x_5963_ = v_reuseFailAlloc_5964_;
                                                    state = 8;
                                                    continue;
                                                }
                                            } else {
                                                lean_del_object(v___x_5880_);
                                                v___x_5965_ =
                                                    lean_nat_dec_eq(v_val_5911_, v___x_5874_);
                                                if v___x_5965_ == 0 {
                                                    v___y_5913_ = v___x_5965_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    v___x_5966_ =
                                                        lean_string_utf8_byte_size(v_a_5883_);
                                                    v___x_5967_ =
                                                        lean_nat_dec_eq(v___x_5966_, v___x_5874_);
                                                    v___y_5913_ = v___x_5967_;
                                                    state = 4;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_5910_);
                                        lean_dec(v_val_5908_);
                                        lean_dec(v_val_5905_);
                                        lean_dec(v_a_5883_);
                                        lean_del_object(v___x_5880_);
                                        lean_dec_ref(v_ands_5872_);
                                        v_str_5968_ = lean_ctor_get(v___x_5909_, 0);
                                        lean_inc_ref(v_str_5968_);
                                        v_startInclusive_5969_ = lean_ctor_get(v___x_5909_, 1);
                                        lean_inc(v_startInclusive_5969_);
                                        v_endExclusive_5970_ = lean_ctor_get(v___x_5909_, 2);
                                        lean_inc(v_endExclusive_5970_);
                                        lean_dec(v___x_5909_);
                                        v___x_5971_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__3;
                                        v___x_5972_ = lean_string_utf8_extract(
                                            v_str_5968_,
                                            v_startInclusive_5969_,
                                            v_endExclusive_5970_,
                                        );
                                        lean_dec(v_endExclusive_5970_);
                                        lean_dec(v_startInclusive_5969_);
                                        lean_dec_ref(v_str_5968_);
                                        v___x_5973_ = lean_string_append(v___x_5971_, v___x_5972_);
                                        lean_dec_ref(v___x_5972_);
                                        v___x_5974_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                        v___x_5975_ = lean_string_append(v___x_5973_, v___x_5974_);
                                        if v_isShared_5887_ == 0 {
                                            lean_ctor_set_tag(v___x_5886_, 1);
                                            lean_ctor_set(v___x_5886_, 0, v___x_5975_);
                                            v___x_5977_ = v___x_5886_;
                                            state = 9;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_5978_ =
                                                lean_alloc_ctor(1, 2, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_5978_, 0, v___x_5975_);
                                            lean_ctor_set(v_reuseFailAlloc_5978_, 1, v_a_5884_);
                                            v___x_5977_ = v_reuseFailAlloc_5978_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_inc(v___x_5906_);
                                    lean_dec(v___x_5907_);
                                    lean_dec(v_val_5905_);
                                    lean_dec(v_a_5883_);
                                    lean_del_object(v___x_5880_);
                                    lean_dec(v_a_5877_);
                                    lean_dec_ref(v_ands_5872_);
                                    v_str_5979_ = lean_ctor_get(v___x_5906_, 0);
                                    lean_inc_ref(v_str_5979_);
                                    v_startInclusive_5980_ = lean_ctor_get(v___x_5906_, 1);
                                    lean_inc(v_startInclusive_5980_);
                                    v_endExclusive_5981_ = lean_ctor_get(v___x_5906_, 2);
                                    lean_inc(v_endExclusive_5981_);
                                    lean_dec(v___x_5906_);
                                    v___x_5982_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4;
                                    v___x_5983_ = lean_string_utf8_extract(
                                        v_str_5979_,
                                        v_startInclusive_5980_,
                                        v_endExclusive_5981_,
                                    );
                                    lean_dec(v_endExclusive_5981_);
                                    lean_dec(v_startInclusive_5980_);
                                    lean_dec_ref(v_str_5979_);
                                    v___x_5984_ = lean_string_append(v___x_5982_, v___x_5983_);
                                    lean_dec_ref(v___x_5983_);
                                    v___x_5985_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                    v___x_5986_ = lean_string_append(v___x_5984_, v___x_5985_);
                                    if v_isShared_5887_ == 0 {
                                        lean_ctor_set_tag(v___x_5886_, 1);
                                        lean_ctor_set(v___x_5886_, 0, v___x_5986_);
                                        v___x_5988_ = v___x_5886_;
                                        state = 10;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5986_);
                                        lean_ctor_set(v_reuseFailAlloc_5989_, 1, v_a_5884_);
                                        v___x_5988_ = v_reuseFailAlloc_5989_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                lean_inc(v___x_5903_);
                                lean_dec(v___x_5904_);
                                lean_dec(v_a_5883_);
                                lean_del_object(v___x_5880_);
                                lean_dec(v_a_5877_);
                                lean_dec_ref(v_ands_5872_);
                                v_str_5990_ = lean_ctor_get(v___x_5903_, 0);
                                lean_inc_ref(v_str_5990_);
                                v_startInclusive_5991_ = lean_ctor_get(v___x_5903_, 1);
                                lean_inc(v_startInclusive_5991_);
                                v_endExclusive_5992_ = lean_ctor_get(v___x_5903_, 2);
                                lean_inc(v_endExclusive_5992_);
                                lean_dec(v___x_5903_);
                                v___x_5993_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5;
                                v___x_5994_ = lean_string_utf8_extract(
                                    v_str_5990_,
                                    v_startInclusive_5991_,
                                    v_endExclusive_5992_,
                                );
                                lean_dec(v_endExclusive_5992_);
                                lean_dec(v_startInclusive_5991_);
                                lean_dec_ref(v_str_5990_);
                                v___x_5995_ = lean_string_append(v___x_5993_, v___x_5994_);
                                lean_dec_ref(v___x_5994_);
                                v___x_5996_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                v___x_5997_ = lean_string_append(v___x_5995_, v___x_5996_);
                                if v_isShared_5887_ == 0 {
                                    lean_ctor_set_tag(v___x_5886_, 1);
                                    lean_ctor_set(v___x_5886_, 0, v___x_5997_);
                                    v___x_5999_ = v___x_5886_;
                                    state = 11;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6000_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6000_, 0, v___x_5997_);
                                    lean_ctor_set(v_reuseFailAlloc_6000_, 1, v_a_5884_);
                                    v___x_5999_ = v_reuseFailAlloc_6000_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5880_);
                        v___x_6001_ = lean_array_fget_borrowed(v_a_5877_, v___x_5874_);
                        v___x_6002_ = l_String_Slice_toNat_x3f(v___x_6001_);
                        if lean_obj_tag(v___x_6002_) == 1 {
                            v_val_6003_ = lean_ctor_get(v___x_6002_, 0);
                            lean_inc(v_val_6003_);
                            lean_dec_ref_known(v___x_6002_, 1);
                            v___x_6004_ = lean_array_fget(v_a_5877_, v___x_5889_);
                            lean_dec(v_a_5877_);
                            v___x_6005_ = l_String_Slice_toNat_x3f(v___x_6004_);
                            if lean_obj_tag(v___x_6005_) == 1 {
                                lean_dec(v___x_6004_);
                                v_val_6006_ = lean_ctor_get(v___x_6005_, 0);
                                lean_inc(v_val_6006_);
                                lean_dec_ref_known(v___x_6005_, 1);
                                v___x_6007_ = lean_nat_dec_eq(v_val_6003_, v___x_5874_);
                                if v___x_6007_ == 0 {
                                    lean_inc(v_val_6003_);
                                    v___x_6008_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6008_, 0, v_val_6003_);
                                    lean_ctor_set(v___x_6008_, 1, v_val_6006_);
                                    lean_ctor_set(v___x_6008_, 2, v___x_5874_);
                                    v___x_6009_ = lean_nat_add(v_val_6003_, v___x_5889_);
                                    lean_dec(v_val_6003_);
                                    v___x_6010_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6010_, 0, v___x_6009_);
                                    lean_ctor_set(v___x_6010_, 1, v___x_5874_);
                                    lean_ctor_set(v___x_6010_, 2, v___x_5874_);
                                    v_minVer_6011_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_minVer_6011_, 0, v___x_6008_);
                                    lean_ctor_set(v_minVer_6011_, 1, v_a_5883_);
                                    v___x_6012_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                                    v_maxVer_6013_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_maxVer_6013_, 0, v___x_6010_);
                                    lean_ctor_set(v_maxVer_6013_, 1, v___x_6012_);
                                    v___x_6014_ = 3;
                                    v___x_6015_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6015_, 0, v_minVer_6011_);
                                    lean_ctor_set_uint8(
                                        v___x_6015_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6014_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6015_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___x_6007_,
                                    );
                                    v___x_6016_ = lean_array_push(v_ands_5872_, v___x_6015_);
                                    v___x_6017_ = 0;
                                    v___x_6018_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6018_, 0, v_maxVer_6013_);
                                    lean_ctor_set_uint8(
                                        v___x_6018_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6017_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6018_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___x_5892_,
                                    );
                                    v___x_6019_ = lean_array_push(v___x_6016_, v___x_6018_);
                                    if v_isShared_5887_ == 0 {
                                        lean_ctor_set(v___x_5886_, 0, v___x_6019_);
                                        v___x_6021_ = v___x_5886_;
                                        state = 12;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6022_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6022_, 0, v___x_6019_);
                                        lean_ctor_set(v_reuseFailAlloc_6022_, 1, v_a_5884_);
                                        v___x_6021_ = v_reuseFailAlloc_6022_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    lean_inc(v_val_6006_);
                                    lean_inc(v_val_6003_);
                                    v___x_6023_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6023_, 0, v_val_6003_);
                                    lean_ctor_set(v___x_6023_, 1, v_val_6006_);
                                    lean_ctor_set(v___x_6023_, 2, v___x_5874_);
                                    v___x_6024_ = lean_nat_add(v_val_6006_, v___x_5889_);
                                    lean_dec(v_val_6006_);
                                    v___x_6025_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6025_, 0, v_val_6003_);
                                    lean_ctor_set(v___x_6025_, 1, v___x_6024_);
                                    lean_ctor_set(v___x_6025_, 2, v___x_5874_);
                                    v_minVer_6026_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_minVer_6026_, 0, v___x_6023_);
                                    lean_ctor_set(v_minVer_6026_, 1, v_a_5883_);
                                    v___x_6027_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                                    v_maxVer_6028_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_maxVer_6028_, 0, v___x_6025_);
                                    lean_ctor_set(v_maxVer_6028_, 1, v___x_6027_);
                                    v___x_6029_ = 3;
                                    v___x_6030_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6030_, 0, v_minVer_6026_);
                                    lean_ctor_set_uint8(
                                        v___x_6030_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6029_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6030_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___x_5890_,
                                    );
                                    v___x_6031_ = lean_array_push(v_ands_5872_, v___x_6030_);
                                    v___x_6032_ = 0;
                                    v___x_6033_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6033_, 0, v_maxVer_6028_);
                                    lean_ctor_set_uint8(
                                        v___x_6033_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6032_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6033_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___x_6007_,
                                    );
                                    v___x_6034_ = lean_array_push(v___x_6031_, v___x_6033_);
                                    if v_isShared_5887_ == 0 {
                                        lean_ctor_set(v___x_5886_, 0, v___x_6034_);
                                        v___x_6036_ = v___x_5886_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6037_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6037_, 0, v___x_6034_);
                                        lean_ctor_set(v_reuseFailAlloc_6037_, 1, v_a_5884_);
                                        v___x_6036_ = v_reuseFailAlloc_6037_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_6005_);
                                lean_dec(v_val_6003_);
                                lean_dec(v_a_5883_);
                                lean_dec_ref(v_ands_5872_);
                                v_str_6038_ = lean_ctor_get(v___x_6004_, 0);
                                lean_inc_ref(v_str_6038_);
                                v_startInclusive_6039_ = lean_ctor_get(v___x_6004_, 1);
                                lean_inc(v_startInclusive_6039_);
                                v_endExclusive_6040_ = lean_ctor_get(v___x_6004_, 2);
                                lean_inc(v_endExclusive_6040_);
                                lean_dec(v___x_6004_);
                                v___x_6041_ = l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__4;
                                v___x_6042_ = lean_string_utf8_extract(
                                    v_str_6038_,
                                    v_startInclusive_6039_,
                                    v_endExclusive_6040_,
                                );
                                lean_dec(v_endExclusive_6040_);
                                lean_dec(v_startInclusive_6039_);
                                lean_dec_ref(v_str_6038_);
                                v___x_6043_ = lean_string_append(v___x_6041_, v___x_6042_);
                                lean_dec_ref(v___x_6042_);
                                v___x_6044_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                                v___x_6045_ = lean_string_append(v___x_6043_, v___x_6044_);
                                if v_isShared_5887_ == 0 {
                                    lean_ctor_set_tag(v___x_5886_, 1);
                                    lean_ctor_set(v___x_5886_, 0, v___x_6045_);
                                    v___x_6047_ = v___x_5886_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_6048_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6045_);
                                    lean_ctor_set(v_reuseFailAlloc_6048_, 1, v_a_5884_);
                                    v___x_6047_ = v_reuseFailAlloc_6048_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc(v___x_6001_);
                            lean_dec(v___x_6002_);
                            lean_dec(v_a_5883_);
                            lean_dec(v_a_5877_);
                            lean_dec_ref(v_ands_5872_);
                            v_str_6049_ = lean_ctor_get(v___x_6001_, 0);
                            lean_inc_ref(v_str_6049_);
                            v_startInclusive_6050_ = lean_ctor_get(v___x_6001_, 1);
                            lean_inc(v_startInclusive_6050_);
                            v_endExclusive_6051_ = lean_ctor_get(v___x_6001_, 2);
                            lean_inc(v_endExclusive_6051_);
                            lean_dec(v___x_6001_);
                            v___x_6052_ =
                                l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5;
                            v___x_6053_ = lean_string_utf8_extract(
                                v_str_6049_,
                                v_startInclusive_6050_,
                                v_endExclusive_6051_,
                            );
                            lean_dec(v_endExclusive_6051_);
                            lean_dec(v_startInclusive_6050_);
                            lean_dec_ref(v_str_6049_);
                            v___x_6054_ = lean_string_append(v___x_6052_, v___x_6053_);
                            lean_dec_ref(v___x_6053_);
                            v___x_6055_ = l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                            v___x_6056_ = lean_string_append(v___x_6054_, v___x_6055_);
                            if v_isShared_5887_ == 0 {
                                lean_ctor_set_tag(v___x_5886_, 1);
                                lean_ctor_set(v___x_5886_, 0, v___x_6056_);
                                v___x_6058_ = v___x_5886_;
                                state = 15;
                                continue;
                            } else {
                                v_reuseFailAlloc_6059_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6059_, 0, v___x_6056_);
                                lean_ctor_set(v_reuseFailAlloc_6059_, 1, v_a_5884_);
                                v___x_6058_ = v_reuseFailAlloc_6059_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_5880_);
                    v___x_6060_ = lean_array_fget(v_a_5877_, v___x_5874_);
                    lean_dec(v_a_5877_);
                    v___x_6061_ = l_String_Slice_toNat_x3f(v___x_6060_);
                    if lean_obj_tag(v___x_6061_) == 1 {
                        lean_dec(v___x_6060_);
                        v_val_6062_ = lean_ctor_get(v___x_6061_, 0);
                        lean_inc_n(v_val_6062_, 2);
                        lean_dec_ref_known(v___x_6061_, 1);
                        v___x_6063_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_6063_, 0, v_val_6062_);
                        lean_ctor_set(v___x_6063_, 1, v___x_5874_);
                        lean_ctor_set(v___x_6063_, 2, v___x_5874_);
                        v___x_6064_ = lean_nat_add(v_val_6062_, v___x_5889_);
                        lean_dec(v_val_6062_);
                        v___x_6065_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_6065_, 0, v___x_6064_);
                        lean_ctor_set(v___x_6065_, 1, v___x_5874_);
                        lean_ctor_set(v___x_6065_, 2, v___x_5874_);
                        v_minVer_6066_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_minVer_6066_, 0, v___x_6063_);
                        lean_ctor_set(v_minVer_6066_, 1, v_a_5883_);
                        v___x_6067_ =
                            l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                        v_maxVer_6068_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_maxVer_6068_, 0, v___x_6065_);
                        lean_ctor_set(v_maxVer_6068_, 1, v___x_6067_);
                        v___x_6069_ = 3;
                        v___x_6070_ = 0;
                        v___x_6071_ = lean_alloc_ctor(0, 1, (2) as u32);
                        lean_ctor_set(v___x_6071_, 0, v_minVer_6066_);
                        lean_ctor_set_uint8(
                            v___x_6071_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_6069_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6071_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            v___x_6070_,
                        );
                        v___x_6072_ = lean_array_push(v_ands_5872_, v___x_6071_);
                        v___x_6073_ = 0;
                        v___x_6074_ = lean_alloc_ctor(0, 1, (2) as u32);
                        lean_ctor_set(v___x_6074_, 0, v_maxVer_6068_);
                        lean_ctor_set_uint8(
                            v___x_6074_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_6073_,
                        );
                        lean_ctor_set_uint8(
                            v___x_6074_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                            v___x_5890_,
                        );
                        v___x_6075_ = lean_array_push(v___x_6072_, v___x_6074_);
                        if v_isShared_5887_ == 0 {
                            lean_ctor_set(v___x_5886_, 0, v___x_6075_);
                            v___x_6077_ = v___x_5886_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_6078_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6075_);
                            lean_ctor_set(v_reuseFailAlloc_6078_, 1, v_a_5884_);
                            v___x_6077_ = v_reuseFailAlloc_6078_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_6061_);
                        lean_dec(v_a_5883_);
                        lean_dec_ref(v_ands_5872_);
                        v_str_6079_ = lean_ctor_get(v___x_6060_, 0);
                        lean_inc_ref(v_str_6079_);
                        v_startInclusive_6080_ = lean_ctor_get(v___x_6060_, 1);
                        lean_inc(v_startInclusive_6080_);
                        v_endExclusive_6081_ = lean_ctor_get(v___x_6060_, 2);
                        lean_inc(v_endExclusive_6081_);
                        lean_dec(v___x_6060_);
                        v___x_6082_ =
                            l___private_Lake_Util_Version_0__Lake_SemVerCore_parseM___closed__5;
                        v___x_6083_ = lean_string_utf8_extract(
                            v_str_6079_,
                            v_startInclusive_6080_,
                            v_endExclusive_6081_,
                        );
                        lean_dec(v_endExclusive_6081_);
                        lean_dec(v_startInclusive_6080_);
                        lean_dec_ref(v_str_6079_);
                        v___x_6084_ = lean_string_append(v___x_6082_, v___x_6083_);
                        lean_dec_ref(v___x_6083_);
                        v___x_6085_ =
                            l___private_Lake_Util_Version_0__Lake_parseVerNat___redArg___closed__2;
                        v___x_6086_ = lean_string_append(v___x_6084_, v___x_6085_);
                        if v_isShared_5887_ == 0 {
                            lean_ctor_set_tag(v___x_5886_, 1);
                            lean_ctor_set(v___x_5886_, 0, v___x_6086_);
                            v___x_6088_ = v___x_5886_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_6089_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6089_, 0, v___x_6086_);
                            lean_ctor_set(v_reuseFailAlloc_6089_, 1, v_a_5884_);
                            v___x_6088_ = v_reuseFailAlloc_6089_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_5901_;
            }
            4 => {
                if v___y_5913_ == 0 {
                    lean_inc(v_val_5911_);
                    lean_inc(v_val_5908_);
                    lean_inc(v_val_5905_);
                    v___x_5914_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5914_, 0, v_val_5905_);
                    lean_ctor_set(v___x_5914_, 1, v_val_5908_);
                    lean_ctor_set(v___x_5914_, 2, v_val_5911_);
                    v___x_5915_ = lean_nat_add(v_val_5911_, v___x_5889_);
                    lean_dec(v_val_5911_);
                    v___x_5916_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_5916_, 0, v_val_5905_);
                    lean_ctor_set(v___x_5916_, 1, v_val_5908_);
                    lean_ctor_set(v___x_5916_, 2, v___x_5915_);
                    v_minVer_5917_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_minVer_5917_, 0, v___x_5914_);
                    lean_ctor_set(v_minVer_5917_, 1, v_a_5883_);
                    v___x_5918_ =
                        l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                    v_maxVer_5919_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_maxVer_5919_, 0, v___x_5916_);
                    lean_ctor_set(v_maxVer_5919_, 1, v___x_5918_);
                    v___x_5920_ = 3;
                    v___x_5921_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_5921_, 0, v_minVer_5917_);
                    lean_ctor_set_uint8(
                        v___x_5921_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5920_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5921_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v___y_5913_,
                    );
                    v___x_5922_ = lean_array_push(v_ands_5872_, v___x_5921_);
                    v___x_5923_ = 0;
                    v___x_5924_ = lean_alloc_ctor(0, 1, (2) as u32);
                    lean_ctor_set(v___x_5924_, 0, v_maxVer_5919_);
                    lean_ctor_set_uint8(
                        v___x_5924_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_5923_,
                    );
                    lean_ctor_set_uint8(
                        v___x_5924_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v___x_5894_,
                    );
                    v___x_5925_ = lean_array_push(v___x_5922_, v___x_5924_);
                    if v_isShared_5887_ == 0 {
                        lean_ctor_set(v___x_5886_, 0, v___x_5925_);
                        v___x_5927_ = v___x_5886_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5928_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5928_, 0, v___x_5925_);
                        lean_ctor_set(v_reuseFailAlloc_5928_, 1, v_a_5884_);
                        v___x_5927_ = v_reuseFailAlloc_5928_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_val_5911_);
                    lean_dec(v_val_5908_);
                    lean_dec(v_val_5905_);
                    lean_dec(v_a_5883_);
                    lean_dec_ref(v_ands_5872_);
                    v___x_5929_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret___closed__1;
                    if v_isShared_5887_ == 0 {
                        lean_ctor_set_tag(v___x_5886_, 1);
                        lean_ctor_set(v___x_5886_, 0, v___x_5929_);
                        v___x_5931_ = v___x_5886_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5932_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5932_, 0, v___x_5929_);
                        lean_ctor_set(v_reuseFailAlloc_5932_, 1, v_a_5884_);
                        v___x_5931_ = v_reuseFailAlloc_5932_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5927_;
            }
            6 => {
                return v___x_5931_;
            }
            7 => {
                return v___x_5947_;
            }
            8 => {
                return v___x_5963_;
            }
            9 => {
                return v___x_5977_;
            }
            10 => {
                return v___x_5988_;
            }
            11 => {
                return v___x_5999_;
            }
            12 => {
                return v___x_6021_;
            }
            13 => {
                return v___x_6036_;
            }
            14 => {
                return v___x_6047_;
            }
            15 => {
                return v___x_6058_;
            }
            16 => {
                return v___x_6077_;
            }
            17 => {
                return v___x_6088_;
            }
            18 => {
                if v_isShared_6095_ == 0 {
                    v___x_6097_ = v___x_6094_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6091_);
                    lean_ctor_set(v_reuseFailAlloc_6098_, 1, v_a_6092_);
                    v___x_6097_ = v_reuseFailAlloc_6098_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(
    mut v_s_6106_: *mut LeanObject,
    mut v_ands_6107_: *mut LeanObject,
    mut v_a_6108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6129_: u8 = 0;
    let mut v___y_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6136_: u8 = 0;
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: u8 = 0;
    let mut v_n_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: u8 = 0;
    let mut v___x_6149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: u8 = 0;
    let mut v___x_6152_: u8 = 0;
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minVer_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxVer_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: u8 = 0;
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: u8 = 0;
    let mut v___x_6169_: u8 = 0;
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6199_: u8 = 0;
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: u8 = 0;
    let mut v_val_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: u32 = 0;
    let mut v___x_6206_: u32 = 0;
    let mut v___x_6207_: u8 = 0;
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6212_: u8 = 0;
    let mut v_a_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6217_: u8 = 0;
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6221_: u8 = 0;
    let mut v___y_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: u8 = 0;
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6242_: u8 = 0;
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6246_: u8 = 0;
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: u8 = 0;
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6264_: u8 = 0;
    let mut v___x_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6268_: u8 = 0;
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: u8 = 0;
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6274_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6122_ = lean_unsigned_to_nat(0);
                v___x_6123_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents___closed__0;
                lean_inc(v_a_6108_);
                lean_inc_ref(v_s_6106_);
                v___x_6124_ = l___private_Lake_Util_Version_0__Lake_parseVerComponents_go___redArg(
                    v_s_6106_,
                    v___x_6123_,
                    v_a_6108_,
                    v_a_6108_,
                );
                v_a_6125_ = lean_ctor_get(v___x_6124_, 0);
                v_a_6126_ = lean_ctor_get(v___x_6124_, 1);
                v_isSharedCheck_6274_ = (!lean_is_exclusive(v___x_6124_)) as u8;
                if v_isSharedCheck_6274_ == 0 {
                    v___x_6128_ = v___x_6124_;
                    v_isShared_6129_ = v_isSharedCheck_6274_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_a_6126_);
                    lean_inc(v_a_6125_);
                    lean_dec(v___x_6124_);
                    v___x_6128_ = lean_box(0);
                    v_isShared_6129_ = v_isSharedCheck_6274_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_6111_ =
                    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__0;
                v___x_6112_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6112_, 0, v___x_6111_);
                lean_ctor_set(v___x_6112_, 1, v___y_6110_);
                return v___x_6112_;
            }
            2 => {
                v___x_6115_ = l_Lake_VerComparator_wild;
                v___x_6116_ = lean_array_push(v_ands_6107_, v___x_6115_);
                v___x_6117_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6117_, 0, v___x_6116_);
                lean_ctor_set(v___x_6117_, 1, v___y_6114_);
                return v___x_6117_;
            }
            3 => {
                v___x_6120_ =
                    l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__1;
                v___x_6121_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6121_, 0, v___x_6120_);
                lean_ctor_set(v___x_6121_, 1, v___y_6119_);
                return v___x_6121_;
            }
            4 => {
                v___x_6247_ = l_Lake_instReprSemVerCore_repr___redArg___closed__1;
                v___x_6269_ = lean_array_get_size(v_a_6125_);
                v___x_6270_ = lean_nat_dec_lt(v___x_6122_, v___x_6269_);
                if v___x_6270_ == 0 {
                    v___x_6271_ = lean_box(0);
                    v___y_6249_ = v___x_6271_;
                    state = 18;
                    continue;
                } else {
                    v___x_6272_ = lean_array_fget_borrowed(v_a_6125_, v___x_6122_);
                    lean_inc(v___x_6272_);
                    v___x_6273_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6273_, 0, v___x_6272_);
                    v___y_6249_ = v___x_6273_;
                    state = 18;
                    continue;
                }
            }
            5 => {
                v___x_6137_ = lean_unsigned_to_nat(3);
                v___x_6138_ = lean_array_get_size(v_a_6125_);
                lean_dec(v_a_6125_);
                v___x_6139_ = lean_nat_dec_lt(v___x_6137_, v___x_6138_);
                if v___x_6139_ == 0 {
                    match lean_obj_tag(v___y_6131_) {
                        2 => match lean_obj_tag(v___y_6133_) {
                            2 => {
                                if lean_obj_tag(v___y_6135_) == 1 {
                                    v_n_6140_ = lean_ctor_get(v___y_6131_, 0);
                                    lean_inc_n(v_n_6140_, 2);
                                    lean_dec_ref_known(v___y_6131_, 1);
                                    v_n_6141_ = lean_ctor_get(v___y_6133_, 0);
                                    lean_inc_n(v_n_6141_, 2);
                                    lean_dec_ref_known(v___y_6133_, 1);
                                    v___x_6142_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6142_, 0, v_n_6140_);
                                    lean_ctor_set(v___x_6142_, 1, v_n_6141_);
                                    lean_ctor_set(v___x_6142_, 2, v___x_6122_);
                                    v___x_6143_ = lean_nat_add(v_n_6141_, v___y_6134_);
                                    lean_dec(v_n_6141_);
                                    v___x_6144_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6144_, 0, v_n_6140_);
                                    lean_ctor_set(v___x_6144_, 1, v___x_6143_);
                                    lean_ctor_set(v___x_6144_, 2, v___x_6122_);
                                    v___x_6145_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                                    v_minVer_6146_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_minVer_6146_, 0, v___x_6142_);
                                    lean_ctor_set(v_minVer_6146_, 1, v___x_6145_);
                                    v_maxVer_6147_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_maxVer_6147_, 0, v___x_6144_);
                                    lean_ctor_set(v_maxVer_6147_, 1, v___x_6145_);
                                    v___x_6148_ = 3;
                                    v___x_6149_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6149_, 0, v_minVer_6146_);
                                    lean_ctor_set_uint8(
                                        v___x_6149_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6148_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6149_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___y_6136_,
                                    );
                                    v___x_6150_ = lean_array_push(v_ands_6107_, v___x_6149_);
                                    v___x_6151_ = 0;
                                    v___x_6152_ = 1;
                                    v___x_6153_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6153_, 0, v_maxVer_6147_);
                                    lean_ctor_set_uint8(
                                        v___x_6153_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6151_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6153_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___x_6152_,
                                    );
                                    v___x_6154_ = lean_array_push(v___x_6150_, v___x_6153_);
                                    if v_isShared_6129_ == 0 {
                                        lean_ctor_set(v___x_6128_, 1, v___y_6132_);
                                        lean_ctor_set(v___x_6128_, 0, v___x_6154_);
                                        v___x_6156_ = v___x_6128_;
                                        state = 6;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6157_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6157_, 0, v___x_6154_);
                                        lean_ctor_set(v_reuseFailAlloc_6157_, 1, v___y_6132_);
                                        v___x_6156_ = v_reuseFailAlloc_6157_;
                                        state = 6;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v___y_6133_, 1);
                                    lean_dec_ref_known(v___y_6131_, 1);
                                    lean_dec(v___y_6135_);
                                    lean_del_object(v___x_6128_);
                                    lean_dec_ref(v_ands_6107_);
                                    v___y_6119_ = v___y_6132_;
                                    state = 3;
                                    continue;
                                }
                            }
                            1 => {
                                if lean_obj_tag(v___y_6135_) == 2 {
                                    lean_dec_ref_known(v___y_6135_, 1);
                                    lean_dec_ref_known(v___y_6131_, 1);
                                    lean_del_object(v___x_6128_);
                                    lean_dec_ref(v_ands_6107_);
                                    v___y_6110_ = v___y_6132_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___y_6135_);
                                    v_n_6158_ = lean_ctor_get(v___y_6131_, 0);
                                    lean_inc_n(v_n_6158_, 2);
                                    lean_dec_ref_known(v___y_6131_, 1);
                                    v___x_6159_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6159_, 0, v_n_6158_);
                                    lean_ctor_set(v___x_6159_, 1, v___x_6122_);
                                    lean_ctor_set(v___x_6159_, 2, v___x_6122_);
                                    v___x_6160_ = lean_nat_add(v_n_6158_, v___y_6134_);
                                    lean_dec(v_n_6158_);
                                    v___x_6161_ = lean_alloc_ctor(0, 3, (0) as u32);
                                    lean_ctor_set(v___x_6161_, 0, v___x_6160_);
                                    lean_ctor_set(v___x_6161_, 1, v___x_6122_);
                                    lean_ctor_set(v___x_6161_, 2, v___x_6122_);
                                    v___x_6162_ = l___private_Lake_Util_Version_0__Lake_parseSpecialDescr___closed__1;
                                    v_minVer_6163_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_minVer_6163_, 0, v___x_6159_);
                                    lean_ctor_set(v_minVer_6163_, 1, v___x_6162_);
                                    v_maxVer_6164_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v_maxVer_6164_, 0, v___x_6161_);
                                    lean_ctor_set(v_maxVer_6164_, 1, v___x_6162_);
                                    v___x_6165_ = 3;
                                    v___x_6166_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6166_, 0, v_minVer_6163_);
                                    lean_ctor_set_uint8(
                                        v___x_6166_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6165_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6166_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___y_6136_,
                                    );
                                    v___x_6167_ = lean_array_push(v_ands_6107_, v___x_6166_);
                                    v___x_6168_ = 0;
                                    v___x_6169_ = 1;
                                    v___x_6170_ = lean_alloc_ctor(0, 1, (2) as u32);
                                    lean_ctor_set(v___x_6170_, 0, v_maxVer_6164_);
                                    lean_ctor_set_uint8(
                                        v___x_6170_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                                        v___x_6168_,
                                    );
                                    lean_ctor_set_uint8(
                                        v___x_6170_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                        v___x_6169_,
                                    );
                                    v___x_6171_ = lean_array_push(v___x_6167_, v___x_6170_);
                                    if v_isShared_6129_ == 0 {
                                        lean_ctor_set(v___x_6128_, 1, v___y_6132_);
                                        lean_ctor_set(v___x_6128_, 0, v___x_6171_);
                                        v___x_6173_ = v___x_6128_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6174_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6174_, 0, v___x_6171_);
                                        lean_ctor_set(v_reuseFailAlloc_6174_, 1, v___y_6132_);
                                        v___x_6173_ = v_reuseFailAlloc_6174_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                            _ => {
                                lean_dec_ref_known(v___y_6131_, 1);
                                lean_dec(v___y_6135_);
                                lean_dec(v___y_6133_);
                                lean_del_object(v___x_6128_);
                                lean_dec_ref(v_ands_6107_);
                                v___y_6119_ = v___y_6132_;
                                state = 3;
                                continue;
                            }
                        },
                        1 => {
                            if lean_obj_tag(v___y_6135_) == 2 {
                                lean_dec_ref_known(v___y_6135_, 1);
                                lean_dec(v___y_6133_);
                                lean_del_object(v___x_6128_);
                                lean_dec_ref(v_ands_6107_);
                                v___y_6110_ = v___y_6132_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___y_6135_);
                                if lean_obj_tag(v___y_6133_) == 2 {
                                    lean_dec_ref_known(v___y_6133_, 1);
                                    lean_dec_ref(v_ands_6107_);
                                    v___x_6175_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__2;
                                    if v_isShared_6129_ == 0 {
                                        lean_ctor_set_tag(v___x_6128_, 1);
                                        lean_ctor_set(v___x_6128_, 1, v___y_6132_);
                                        lean_ctor_set(v___x_6128_, 0, v___x_6175_);
                                        v___x_6177_ = v___x_6128_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_6178_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_6178_, 0, v___x_6175_);
                                        lean_ctor_set(v_reuseFailAlloc_6178_, 1, v___y_6132_);
                                        v___x_6177_ = v_reuseFailAlloc_6178_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___y_6133_);
                                    lean_del_object(v___x_6128_);
                                    v___y_6114_ = v___y_6132_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            lean_dec(v___y_6131_);
                            lean_del_object(v___x_6128_);
                            if lean_obj_tag(v___y_6133_) == 1 {
                                if lean_obj_tag(v___y_6135_) == 2 {
                                    lean_dec_ref_known(v___y_6135_, 1);
                                    lean_dec_ref(v_ands_6107_);
                                    v___y_6110_ = v___y_6132_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v___y_6135_);
                                    v___y_6114_ = v___y_6132_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v___y_6135_);
                                lean_dec(v___y_6133_);
                                v___y_6114_ = v___y_6132_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v___y_6135_);
                    lean_dec(v___y_6133_);
                    lean_dec(v___y_6131_);
                    lean_dec_ref(v_ands_6107_);
                    v___x_6179_ =
                        l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__3;
                    v___x_6180_ = l_Nat_reprFast(v___x_6138_);
                    v___x_6181_ = lean_string_append(v___x_6179_, v___x_6180_);
                    lean_dec_ref(v___x_6180_);
                    v___x_6182_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde___closed__1;
                    v___x_6183_ = lean_string_append(v___x_6181_, v___x_6182_);
                    if v_isShared_6129_ == 0 {
                        lean_ctor_set_tag(v___x_6128_, 1);
                        lean_ctor_set(v___x_6128_, 1, v___y_6132_);
                        lean_ctor_set(v___x_6128_, 0, v___x_6183_);
                        v___x_6185_ = v___x_6128_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6186_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6186_, 0, v___x_6183_);
                        lean_ctor_set(v_reuseFailAlloc_6186_, 1, v___y_6132_);
                        v___x_6185_ = v_reuseFailAlloc_6186_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_6156_;
            }
            7 => {
                return v___x_6173_;
            }
            8 => {
                return v___x_6177_;
            }
            9 => {
                return v___x_6185_;
            }
            10 => {
                v___x_6194_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(
                    v___y_6189_,
                    v___y_6193_,
                    v___y_6192_,
                );
                lean_dec(v___y_6193_);
                if lean_obj_tag(v___x_6194_) == 0 {
                    v_a_6195_ = lean_ctor_get(v___x_6194_, 0);
                    v_a_6196_ = lean_ctor_get(v___x_6194_, 1);
                    v_isSharedCheck_6212_ = (!lean_is_exclusive(v___x_6194_)) as u8;
                    if v_isSharedCheck_6212_ == 0 {
                        v___x_6198_ = v___x_6194_;
                        v_isShared_6199_ = v_isSharedCheck_6212_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_6196_);
                        lean_inc(v_a_6195_);
                        lean_dec(v___x_6194_);
                        v___x_6198_ = lean_box(0);
                        v_isShared_6199_ = v_isSharedCheck_6212_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v___y_6190_);
                    lean_dec(v___y_6188_);
                    lean_del_object(v___x_6128_);
                    lean_dec(v_a_6125_);
                    lean_dec_ref(v_ands_6107_);
                    lean_dec_ref(v_s_6106_);
                    v_a_6213_ = lean_ctor_get(v___x_6194_, 0);
                    v_a_6214_ = lean_ctor_get(v___x_6194_, 1);
                    v_isSharedCheck_6221_ = (!lean_is_exclusive(v___x_6194_)) as u8;
                    if v_isSharedCheck_6221_ == 0 {
                        v___x_6216_ = v___x_6194_;
                        v_isShared_6217_ = v_isSharedCheck_6221_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_6214_);
                        lean_inc(v_a_6213_);
                        lean_dec(v___x_6194_);
                        v___x_6216_ = lean_box(0);
                        v_isShared_6217_ = v_isSharedCheck_6221_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                v___x_6200_ = lean_string_utf8_byte_size(v_s_6106_);
                v___x_6201_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6201_, 0, v_s_6106_);
                lean_ctor_set(v___x_6201_, 1, v___x_6122_);
                lean_ctor_set(v___x_6201_, 2, v___x_6200_);
                v___x_6202_ = l_String_Slice_Pos_get_x3f(v___x_6201_, v_a_6196_);
                lean_dec_ref_known(v___x_6201_, 3);
                if lean_obj_tag(v___x_6202_) == 0 {
                    lean_del_object(v___x_6198_);
                    v___x_6203_ = 0;
                    v___y_6131_ = v___y_6188_;
                    v___y_6132_ = v_a_6196_;
                    v___y_6133_ = v___y_6190_;
                    v___y_6134_ = v___y_6191_;
                    v___y_6135_ = v_a_6195_;
                    v___y_6136_ = v___x_6203_;
                    state = 5;
                    continue;
                } else {
                    v_val_6204_ = lean_ctor_get(v___x_6202_, 0);
                    lean_inc(v_val_6204_);
                    lean_dec_ref_known(v___x_6202_, 1);
                    v___x_6205_ = 45;
                    v___x_6206_ = lean_unbox_uint32(v_val_6204_);
                    lean_dec(v_val_6204_);
                    v___x_6207_ = lean_uint32_dec_eq(v___x_6206_, v___x_6205_);
                    if v___x_6207_ == 0 {
                        lean_del_object(v___x_6198_);
                        v___y_6131_ = v___y_6188_;
                        v___y_6132_ = v_a_6196_;
                        v___y_6133_ = v___y_6190_;
                        v___y_6134_ = v___y_6191_;
                        v___y_6135_ = v_a_6195_;
                        v___y_6136_ = v___x_6207_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v_a_6195_);
                        lean_dec(v___y_6190_);
                        lean_dec(v___y_6188_);
                        lean_del_object(v___x_6128_);
                        lean_dec(v_a_6125_);
                        lean_dec_ref(v_ands_6107_);
                        v___x_6208_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild___closed__4;
                        if v_isShared_6199_ == 0 {
                            lean_ctor_set_tag(v___x_6198_, 1);
                            lean_ctor_set(v___x_6198_, 0, v___x_6208_);
                            v___x_6210_ = v___x_6198_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_6211_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6211_, 0, v___x_6208_);
                            lean_ctor_set(v_reuseFailAlloc_6211_, 1, v_a_6196_);
                            v___x_6210_ = v_reuseFailAlloc_6211_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            12 => {
                return v___x_6210_;
            }
            13 => {
                if v_isShared_6217_ == 0 {
                    v___x_6219_ = v___x_6216_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6220_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6220_, 0, v_a_6213_);
                    lean_ctor_set(v_reuseFailAlloc_6220_, 1, v_a_6214_);
                    v___x_6219_ = v_reuseFailAlloc_6220_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6219_;
            }
            15 => {
                v___x_6228_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(
                    v___y_6224_,
                    v___y_6227_,
                    v___y_6226_,
                );
                lean_dec(v___y_6227_);
                if lean_obj_tag(v___x_6228_) == 0 {
                    v_a_6229_ = lean_ctor_get(v___x_6228_, 0);
                    lean_inc(v_a_6229_);
                    v_a_6230_ = lean_ctor_get(v___x_6228_, 1);
                    lean_inc(v_a_6230_);
                    lean_dec_ref_known(v___x_6228_, 2);
                    v___x_6231_ = l_Lake_instReprSemVerCore_repr___redArg___closed__12;
                    v___x_6232_ = lean_unsigned_to_nat(2);
                    v___x_6233_ = lean_array_get_size(v_a_6125_);
                    v___x_6234_ = lean_nat_dec_lt(v___x_6232_, v___x_6233_);
                    if v___x_6234_ == 0 {
                        v___x_6235_ = lean_box(0);
                        v___y_6188_ = v___y_6223_;
                        v___y_6189_ = v___x_6231_;
                        v___y_6190_ = v_a_6229_;
                        v___y_6191_ = v___y_6225_;
                        v___y_6192_ = v_a_6230_;
                        v___y_6193_ = v___x_6235_;
                        state = 10;
                        continue;
                    } else {
                        v___x_6236_ = lean_array_fget_borrowed(v_a_6125_, v___x_6232_);
                        lean_inc(v___x_6236_);
                        v___x_6237_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6237_, 0, v___x_6236_);
                        v___y_6188_ = v___y_6223_;
                        v___y_6189_ = v___x_6231_;
                        v___y_6190_ = v_a_6229_;
                        v___y_6191_ = v___y_6225_;
                        v___y_6192_ = v_a_6230_;
                        v___y_6193_ = v___x_6237_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v___y_6223_);
                    lean_del_object(v___x_6128_);
                    lean_dec(v_a_6125_);
                    lean_dec_ref(v_ands_6107_);
                    lean_dec_ref(v_s_6106_);
                    v_a_6238_ = lean_ctor_get(v___x_6228_, 0);
                    v_a_6239_ = lean_ctor_get(v___x_6228_, 1);
                    v_isSharedCheck_6246_ = (!lean_is_exclusive(v___x_6228_)) as u8;
                    if v_isSharedCheck_6246_ == 0 {
                        v___x_6241_ = v___x_6228_;
                        v_isShared_6242_ = v_isSharedCheck_6246_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_6239_);
                        lean_inc(v_a_6238_);
                        lean_dec(v___x_6228_);
                        v___x_6241_ = lean_box(0);
                        v_isShared_6242_ = v_isSharedCheck_6246_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_6242_ == 0 {
                    v___x_6244_ = v___x_6241_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6245_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6245_, 0, v_a_6238_);
                    lean_ctor_set(v_reuseFailAlloc_6245_, 1, v_a_6239_);
                    v___x_6244_ = v_reuseFailAlloc_6245_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6244_;
            }
            18 => {
                v___x_6250_ = l___private_Lake_Util_Version_0__Lake_parseVerComponent___redArg(
                    v___x_6247_,
                    v___y_6249_,
                    v_a_6126_,
                );
                lean_dec(v___y_6249_);
                if lean_obj_tag(v___x_6250_) == 0 {
                    v_a_6251_ = lean_ctor_get(v___x_6250_, 0);
                    lean_inc(v_a_6251_);
                    v_a_6252_ = lean_ctor_get(v___x_6250_, 1);
                    lean_inc(v_a_6252_);
                    lean_dec_ref_known(v___x_6250_, 2);
                    v___x_6253_ = l_Lake_instReprSemVerCore_repr___redArg___closed__10;
                    v___x_6254_ = lean_unsigned_to_nat(1);
                    v___x_6255_ = lean_array_get_size(v_a_6125_);
                    v___x_6256_ = lean_nat_dec_lt(v___x_6254_, v___x_6255_);
                    if v___x_6256_ == 0 {
                        v___x_6257_ = lean_box(0);
                        v___y_6223_ = v_a_6251_;
                        v___y_6224_ = v___x_6253_;
                        v___y_6225_ = v___x_6254_;
                        v___y_6226_ = v_a_6252_;
                        v___y_6227_ = v___x_6257_;
                        state = 15;
                        continue;
                    } else {
                        v___x_6258_ = lean_array_fget_borrowed(v_a_6125_, v___x_6254_);
                        lean_inc(v___x_6258_);
                        v___x_6259_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_6259_, 0, v___x_6258_);
                        v___y_6223_ = v_a_6251_;
                        v___y_6224_ = v___x_6253_;
                        v___y_6225_ = v___x_6254_;
                        v___y_6226_ = v_a_6252_;
                        v___y_6227_ = v___x_6259_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6128_);
                    lean_dec(v_a_6125_);
                    lean_dec_ref(v_ands_6107_);
                    lean_dec_ref(v_s_6106_);
                    v_a_6260_ = lean_ctor_get(v___x_6250_, 0);
                    v_a_6261_ = lean_ctor_get(v___x_6250_, 1);
                    v_isSharedCheck_6268_ = (!lean_is_exclusive(v___x_6250_)) as u8;
                    if v_isSharedCheck_6268_ == 0 {
                        v___x_6263_ = v___x_6250_;
                        v_isShared_6264_ = v_isSharedCheck_6268_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_6261_);
                        lean_inc(v_a_6260_);
                        lean_dec(v___x_6250_);
                        v___x_6263_ = lean_box(0);
                        v_isShared_6264_ = v_isSharedCheck_6268_;
                        state = 19;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_6264_ == 0 {
                    v___x_6266_ = v___x_6263_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6267_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6267_, 0, v_a_6260_);
                    lean_ctor_set(v_reuseFailAlloc_6267_, 1, v_a_6261_);
                    v___x_6266_ = v_reuseFailAlloc_6267_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(
    mut v_s_6281_: *mut LeanObject,
    mut v_needsRange_6282_: u8,
    mut v_ors_6283_: *mut LeanObject,
    mut v_ands_6284_: *mut LeanObject,
    mut v_p_6285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: u8 = 0;
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6303_: u8 = 0;
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6307_: u8 = 0;
    let mut v_c_6308_: u32 = 0;
    let mut v___y_6310_: u8 = 0;
    let mut v___y_6311_: u8 = 0;
    let mut v___x_6312_: u32 = 0;
    let mut v___x_6313_: u8 = 0;
    let mut v___x_6314_: u32 = 0;
    let mut v___x_6315_: u8 = 0;
    let mut v___x_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6325_: u8 = 0;
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6329_: u8 = 0;
    let mut v_p_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: u8 = 0;
    let mut v___x_6332_: u32 = 0;
    let mut v___x_6333_: u8 = 0;
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: u8 = 0;
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6352_: u8 = 0;
    let mut v___y_6353_: u8 = 0;
    let mut v___x_6354_: u32 = 0;
    let mut v___x_6355_: u8 = 0;
    let mut v___x_6356_: u32 = 0;
    let mut v___x_6357_: u8 = 0;
    let mut v___y_6359_: u8 = 0;
    let mut v___x_6360_: u32 = 0;
    let mut v___x_6361_: u8 = 0;
    let mut v___x_6362_: u32 = 0;
    let mut v___x_6363_: u8 = 0;
    let mut v___x_6364_: u32 = 0;
    let mut v___x_6365_: u8 = 0;
    let mut v___x_6366_: u8 = 0;
    let mut v___x_6367_: u32 = 0;
    let mut v___x_6368_: u8 = 0;
    let mut v___x_6369_: u32 = 0;
    let mut v___x_6370_: u8 = 0;
    let mut v_p_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: u8 = 0;
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6381_: u8 = 0;
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6385_: u8 = 0;
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: u8 = 0;
    let mut v___x_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6398_: u8 = 0;
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6402_: u8 = 0;
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6406_: u8 = 0;
    let mut v___x_6407_: u32 = 0;
    let mut v___x_6408_: u8 = 0;
    let mut v___x_6409_: u32 = 0;
    let mut v___x_6410_: u8 = 0;
    let mut v___x_6412_: u32 = 0;
    let mut v___x_6413_: u8 = 0;
    let mut v___x_6414_: u32 = 0;
    let mut v___x_6415_: u8 = 0;
    let mut v___x_6416_: u32 = 0;
    let mut v___x_6417_: u8 = 0;
    let mut v___x_6418_: u32 = 0;
    let mut v___x_6419_: u8 = 0;
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: u8 = 0;
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6292_ = lean_string_utf8_byte_size(v_s_6281_);
                v___x_6293_ = lean_nat_dec_eq(v_p_6285_, v___x_6292_);
                if v___x_6293_ == 0 {
                    v_c_6308_ = lean_string_utf8_get_fast(v_s_6281_, v_p_6285_);
                    v___x_6416_ = 65;
                    v___x_6417_ = lean_uint32_dec_le(v___x_6416_, v_c_6308_);
                    if v___x_6417_ == 0 {
                        state = 16;
                        continue;
                    } else {
                        v___x_6418_ = 90;
                        v___x_6419_ = lean_uint32_dec_le(v_c_6308_, v___x_6418_);
                        if v___x_6419_ == 0 {
                            state = 16;
                            continue;
                        } else {
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_s_6281_);
                    if v_needsRange_6282_ == 0 {
                        v___x_6420_ = lean_array_get_size(v_ands_6284_);
                        v___x_6421_ = lean_unsigned_to_nat(0);
                        v___x_6422_ = lean_nat_dec_eq(v___x_6420_, v___x_6421_);
                        if v___x_6422_ == 0 {
                            v___x_6423_ = lean_array_push(v_ors_6283_, v_ands_6284_);
                            v___x_6424_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_6424_, 0, v___x_6423_);
                            lean_ctor_set(v___x_6424_, 1, v_p_6285_);
                            return v___x_6424_;
                        } else {
                            lean_dec_ref(v_ands_6284_);
                            lean_dec_ref(v_ors_6283_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_ands_6284_);
                        lean_dec_ref(v_ors_6283_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6287_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0;
                v___x_6288_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6288_, 0, v___x_6287_);
                lean_ctor_set(v___x_6288_, 1, v_p_6285_);
                return v___x_6288_;
            }
            2 => {
                v___x_6290_ = lean_string_utf8_next_fast(v_s_6281_, v_p_6285_);
                lean_dec(v_p_6285_);
                v_p_6285_ = v___x_6290_;
                state = 0;
                continue;
            }
            3 => {
                lean_inc_ref(v_s_6281_);
                v___x_6295_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseWild(
                    v_s_6281_,
                    v_ands_6284_,
                    v_p_6285_,
                );
                if lean_obj_tag(v___x_6295_) == 0 {
                    v_a_6296_ = lean_ctor_get(v___x_6295_, 0);
                    lean_inc(v_a_6296_);
                    v_a_6297_ = lean_ctor_get(v___x_6295_, 1);
                    lean_inc(v_a_6297_);
                    lean_dec_ref_known(v___x_6295_, 2);
                    v_needsRange_6282_ = v___x_6293_;
                    v_ands_6284_ = v_a_6296_;
                    v_p_6285_ = v_a_6297_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_ors_6283_);
                    lean_dec_ref(v_s_6281_);
                    v_a_6299_ = lean_ctor_get(v___x_6295_, 0);
                    v_a_6300_ = lean_ctor_get(v___x_6295_, 1);
                    v_isSharedCheck_6307_ = (!lean_is_exclusive(v___x_6295_)) as u8;
                    if v_isSharedCheck_6307_ == 0 {
                        v___x_6302_ = v___x_6295_;
                        v_isShared_6303_ = v_isSharedCheck_6307_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6300_);
                        lean_inc(v_a_6299_);
                        lean_dec(v___x_6295_);
                        v___x_6302_ = lean_box(0);
                        v_isShared_6303_ = v_isSharedCheck_6307_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6303_ == 0 {
                    v___x_6305_ = v___x_6302_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6306_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6306_, 0, v_a_6299_);
                    lean_ctor_set(v_reuseFailAlloc_6306_, 1, v_a_6300_);
                    v___x_6305_ = v_reuseFailAlloc_6306_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6305_;
            }
            6 => {
                if v___y_6311_ == 0 {
                    v___x_6312_ = 44;
                    v___x_6313_ = lean_uint32_dec_eq(v_c_6308_, v___x_6312_);
                    if v___x_6313_ == 0 {
                        v___x_6314_ = 124;
                        v___x_6315_ = lean_uint32_dec_eq(v_c_6308_, v___x_6314_);
                        if v___x_6315_ == 0 {
                            lean_inc_ref(v_s_6281_);
                            v___x_6316_ =
                                l___private_Lake_Util_Version_0__Lake_VerComparator_parseM(
                                    v_s_6281_, v_p_6285_,
                                );
                            if lean_obj_tag(v___x_6316_) == 0 {
                                v_a_6317_ = lean_ctor_get(v___x_6316_, 0);
                                lean_inc(v_a_6317_);
                                v_a_6318_ = lean_ctor_get(v___x_6316_, 1);
                                lean_inc(v_a_6318_);
                                lean_dec_ref_known(v___x_6316_, 2);
                                v___x_6319_ = lean_array_push(v_ands_6284_, v_a_6317_);
                                v_needsRange_6282_ = v___x_6315_;
                                v_ands_6284_ = v___x_6319_;
                                v_p_6285_ = v_a_6318_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec_ref(v_ands_6284_);
                                lean_dec_ref(v_ors_6283_);
                                lean_dec_ref(v_s_6281_);
                                v_a_6321_ = lean_ctor_get(v___x_6316_, 0);
                                v_a_6322_ = lean_ctor_get(v___x_6316_, 1);
                                v_isSharedCheck_6329_ = (!lean_is_exclusive(v___x_6316_)) as u8;
                                if v_isSharedCheck_6329_ == 0 {
                                    v___x_6324_ = v___x_6316_;
                                    v_isShared_6325_ = v_isSharedCheck_6329_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_6322_);
                                    lean_inc(v_a_6321_);
                                    lean_dec(v___x_6316_);
                                    v___x_6324_ = lean_box(0);
                                    v_isShared_6325_ = v_isSharedCheck_6329_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            v_p_6330_ = lean_string_utf8_next_fast(v_s_6281_, v_p_6285_);
                            lean_dec(v_p_6285_);
                            v___x_6331_ = lean_nat_dec_eq(v_p_6330_, v___x_6292_);
                            if v___x_6331_ == 0 {
                                v___x_6332_ = lean_string_utf8_get_fast(v_s_6281_, v_p_6330_);
                                v___x_6333_ = lean_uint32_dec_eq(v___x_6332_, v___x_6314_);
                                if v___x_6333_ == 0 {
                                    lean_dec_ref(v_ands_6284_);
                                    lean_dec_ref(v_ors_6283_);
                                    lean_dec_ref(v_s_6281_);
                                    v___x_6334_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1;
                                    v___x_6335_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_6335_, 0, v___x_6334_);
                                    lean_ctor_set(v___x_6335_, 1, v_p_6330_);
                                    return v___x_6335_;
                                } else {
                                    v___x_6336_ = lean_array_get_size(v_ands_6284_);
                                    v___x_6337_ = lean_unsigned_to_nat(0);
                                    v___x_6338_ = lean_nat_dec_eq(v___x_6336_, v___x_6337_);
                                    if v___x_6338_ == 0 {
                                        v___x_6339_ = lean_array_push(v_ors_6283_, v_ands_6284_);
                                        v___x_6340_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__2;
                                        v___x_6341_ =
                                            lean_string_utf8_next_fast(v_s_6281_, v_p_6330_);
                                        v_needsRange_6282_ = v___y_6310_;
                                        v_ors_6283_ = v___x_6339_;
                                        v_ands_6284_ = v___x_6340_;
                                        v_p_6285_ = v___x_6341_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_ands_6284_);
                                        lean_dec_ref(v_ors_6283_);
                                        lean_dec_ref(v_s_6281_);
                                        v___x_6343_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0;
                                        v___x_6344_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_6344_, 0, v___x_6343_);
                                        lean_ctor_set(v___x_6344_, 1, v_p_6330_);
                                        return v___x_6344_;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_ands_6284_);
                                lean_dec_ref(v_ors_6283_);
                                lean_dec_ref(v_s_6281_);
                                v___x_6345_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__1;
                                v___x_6346_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_6346_, 0, v___x_6345_);
                                lean_ctor_set(v___x_6346_, 1, v_p_6330_);
                                return v___x_6346_;
                            }
                        }
                    } else {
                        if v_needsRange_6282_ == 0 {
                            v___x_6347_ = lean_string_utf8_next_fast(v_s_6281_, v_p_6285_);
                            lean_dec(v_p_6285_);
                            v_needsRange_6282_ = v___y_6310_;
                            v_p_6285_ = v___x_6347_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_ands_6284_);
                            lean_dec_ref(v_ors_6283_);
                            lean_dec_ref(v_s_6281_);
                            v___x_6349_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__0;
                            v___x_6350_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v___x_6350_, 0, v___x_6349_);
                            lean_ctor_set(v___x_6350_, 1, v_p_6285_);
                            return v___x_6350_;
                        }
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            7 => {
                if v_isShared_6325_ == 0 {
                    v___x_6327_ = v___x_6324_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6328_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 0, v_a_6321_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 1, v_a_6322_);
                    v___x_6327_ = v_reuseFailAlloc_6328_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6327_;
            }
            9 => {
                if v___y_6353_ == 0 {
                    v___x_6354_ = 13;
                    v___x_6355_ = lean_uint32_dec_eq(v_c_6308_, v___x_6354_);
                    if v___x_6355_ == 0 {
                        v___x_6356_ = 10;
                        v___x_6357_ = lean_uint32_dec_eq(v_c_6308_, v___x_6356_);
                        v___y_6310_ = v___y_6352_;
                        v___y_6311_ = v___x_6357_;
                        state = 6;
                        continue;
                    } else {
                        v___y_6310_ = v___y_6352_;
                        v___y_6311_ = v___x_6355_;
                        state = 6;
                        continue;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            10 => {
                if v___y_6359_ == 0 {
                    v___x_6360_ = 42;
                    v___x_6361_ = lean_uint32_dec_eq(v_c_6308_, v___x_6360_);
                    if v___x_6361_ == 0 {
                        v___x_6362_ = 94;
                        v___x_6363_ = lean_uint32_dec_eq(v_c_6308_, v___x_6362_);
                        if v___x_6363_ == 0 {
                            v___x_6364_ = 126;
                            v___x_6365_ = lean_uint32_dec_eq(v_c_6308_, v___x_6364_);
                            if v___x_6365_ == 0 {
                                v___x_6366_ = 1;
                                v___x_6367_ = 32;
                                v___x_6368_ = lean_uint32_dec_eq(v_c_6308_, v___x_6367_);
                                if v___x_6368_ == 0 {
                                    v___x_6369_ = 9;
                                    v___x_6370_ = lean_uint32_dec_eq(v_c_6308_, v___x_6369_);
                                    v___y_6352_ = v___x_6366_;
                                    v___y_6353_ = v___x_6370_;
                                    state = 9;
                                    continue;
                                } else {
                                    v___y_6352_ = v___x_6366_;
                                    v___y_6353_ = v___x_6368_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v_p_6371_ = lean_string_utf8_next_fast(v_s_6281_, v_p_6285_);
                                lean_dec(v_p_6285_);
                                v___x_6372_ = lean_nat_dec_eq(v_p_6371_, v___x_6292_);
                                if v___x_6372_ == 0 {
                                    lean_inc_ref(v_s_6281_);
                                    v___x_6373_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseTilde(v_s_6281_, v_ands_6284_, v_p_6371_);
                                    if lean_obj_tag(v___x_6373_) == 0 {
                                        v_a_6374_ = lean_ctor_get(v___x_6373_, 0);
                                        lean_inc(v_a_6374_);
                                        v_a_6375_ = lean_ctor_get(v___x_6373_, 1);
                                        lean_inc(v_a_6375_);
                                        lean_dec_ref_known(v___x_6373_, 2);
                                        v_needsRange_6282_ = v___x_6363_;
                                        v_ands_6284_ = v_a_6374_;
                                        v_p_6285_ = v_a_6375_;
                                        state = 0;
                                        continue;
                                    } else {
                                        lean_dec_ref(v_ors_6283_);
                                        lean_dec_ref(v_s_6281_);
                                        v_a_6377_ = lean_ctor_get(v___x_6373_, 0);
                                        v_a_6378_ = lean_ctor_get(v___x_6373_, 1);
                                        v_isSharedCheck_6385_ =
                                            (!lean_is_exclusive(v___x_6373_)) as u8;
                                        if v_isSharedCheck_6385_ == 0 {
                                            v___x_6380_ = v___x_6373_;
                                            v_isShared_6381_ = v_isSharedCheck_6385_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6378_);
                                            lean_inc(v_a_6377_);
                                            lean_dec(v___x_6373_);
                                            v___x_6380_ = lean_box(0);
                                            v_isShared_6381_ = v_isSharedCheck_6385_;
                                            state = 11;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_ands_6284_);
                                    lean_dec_ref(v_ors_6283_);
                                    lean_dec_ref(v_s_6281_);
                                    v___x_6386_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__3;
                                    v___x_6387_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v___x_6387_, 0, v___x_6386_);
                                    lean_ctor_set(v___x_6387_, 1, v_p_6371_);
                                    return v___x_6387_;
                                }
                            }
                        } else {
                            v_p_6388_ = lean_string_utf8_next_fast(v_s_6281_, v_p_6285_);
                            lean_dec(v_p_6285_);
                            v___x_6389_ = lean_nat_dec_eq(v_p_6388_, v___x_6292_);
                            if v___x_6389_ == 0 {
                                lean_inc_ref(v_s_6281_);
                                v___x_6390_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_parseCaret(v_s_6281_, v_ands_6284_, v_p_6388_);
                                if lean_obj_tag(v___x_6390_) == 0 {
                                    v_a_6391_ = lean_ctor_get(v___x_6390_, 0);
                                    lean_inc(v_a_6391_);
                                    v_a_6392_ = lean_ctor_get(v___x_6390_, 1);
                                    lean_inc(v_a_6392_);
                                    lean_dec_ref_known(v___x_6390_, 2);
                                    v_needsRange_6282_ = v___x_6361_;
                                    v_ands_6284_ = v_a_6391_;
                                    v_p_6285_ = v_a_6392_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_ors_6283_);
                                    lean_dec_ref(v_s_6281_);
                                    v_a_6394_ = lean_ctor_get(v___x_6390_, 0);
                                    v_a_6395_ = lean_ctor_get(v___x_6390_, 1);
                                    v_isSharedCheck_6402_ = (!lean_is_exclusive(v___x_6390_)) as u8;
                                    if v_isSharedCheck_6402_ == 0 {
                                        v___x_6397_ = v___x_6390_;
                                        v_isShared_6398_ = v_isSharedCheck_6402_;
                                        state = 13;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6395_);
                                        lean_inc(v_a_6394_);
                                        lean_dec(v___x_6390_);
                                        v___x_6397_ = lean_box(0);
                                        v_isShared_6398_ = v_isSharedCheck_6402_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_ands_6284_);
                                lean_dec_ref(v_ors_6283_);
                                lean_dec_ref(v_s_6281_);
                                v___x_6403_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___closed__4;
                                v___x_6404_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_6404_, 0, v___x_6403_);
                                lean_ctor_set(v___x_6404_, 1, v_p_6388_);
                                return v___x_6404_;
                            }
                        }
                    } else {
                        state = 3;
                        continue;
                    }
                } else {
                    state = 3;
                    continue;
                }
            }
            11 => {
                if v_isShared_6381_ == 0 {
                    v___x_6383_ = v___x_6380_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6384_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6384_, 0, v_a_6377_);
                    lean_ctor_set(v_reuseFailAlloc_6384_, 1, v_a_6378_);
                    v___x_6383_ = v_reuseFailAlloc_6384_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6383_;
            }
            13 => {
                if v_isShared_6398_ == 0 {
                    v___x_6400_ = v___x_6397_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6401_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6401_, 0, v_a_6394_);
                    lean_ctor_set(v_reuseFailAlloc_6401_, 1, v_a_6395_);
                    v___x_6400_ = v_reuseFailAlloc_6401_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6400_;
            }
            15 => {
                if v___y_6406_ == 0 {
                    v___x_6407_ = 48;
                    v___x_6408_ = lean_uint32_dec_le(v___x_6407_, v_c_6308_);
                    if v___x_6408_ == 0 {
                        v___y_6359_ = v___x_6408_;
                        state = 10;
                        continue;
                    } else {
                        v___x_6409_ = 57;
                        v___x_6410_ = lean_uint32_dec_le(v_c_6308_, v___x_6409_);
                        v___y_6359_ = v___x_6410_;
                        state = 10;
                        continue;
                    }
                } else {
                    state = 3;
                    continue;
                }
            }
            16 => {
                v___x_6412_ = 97;
                v___x_6413_ = lean_uint32_dec_le(v___x_6412_, v_c_6308_);
                if v___x_6413_ == 0 {
                    v___y_6406_ = v___x_6413_;
                    state = 15;
                    continue;
                } else {
                    v___x_6414_ = 122;
                    v___x_6415_ = lean_uint32_dec_le(v_c_6308_, v___x_6414_);
                    v___y_6406_ = v___x_6415_;
                    state = 15;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go___boxed(
    mut v_s_6425_: *mut LeanObject,
    mut v_needsRange_6426_: *mut LeanObject,
    mut v_ors_6427_: *mut LeanObject,
    mut v_ands_6428_: *mut LeanObject,
    mut v_p_6429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_needsRange_boxed_6430_: u8 = 0;
    let mut v_res_6431_: *mut LeanObject = core::ptr::null_mut();
    v_needsRange_boxed_6430_ = (lean_unbox(v_needsRange_6426_) as u8);
    v_res_6431_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(
        v_s_6425_,
        v_needsRange_boxed_6430_,
        v_ors_6427_,
        v_ands_6428_,
        v_p_6429_,
    );
    return v_res_6431_;
}
pub unsafe fn l___private_Lake_Util_Version_0__Lake_VerRange_parseM(
    mut v_s_6434_: *mut LeanObject,
    mut v_a_6435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6436_: u8 = 0;
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6443_: u8 = 0;
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6448_: u8 = 0;
    let mut v_a_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6453_: u8 = 0;
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6436_ = 1;
                v___x_6437_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0;
                lean_inc_ref(v_s_6434_);
                v___x_6438_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(
                    v_s_6434_,
                    v___x_6436_,
                    v___x_6437_,
                    v___x_6437_,
                    v_a_6435_,
                );
                if lean_obj_tag(v___x_6438_) == 0 {
                    v_a_6439_ = lean_ctor_get(v___x_6438_, 0);
                    v_a_6440_ = lean_ctor_get(v___x_6438_, 1);
                    v_isSharedCheck_6448_ = (!lean_is_exclusive(v___x_6438_)) as u8;
                    if v_isSharedCheck_6448_ == 0 {
                        v___x_6442_ = v___x_6438_;
                        v_isShared_6443_ = v_isSharedCheck_6448_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6440_);
                        lean_inc(v_a_6439_);
                        lean_dec(v___x_6438_);
                        v___x_6442_ = lean_box(0);
                        v_isShared_6443_ = v_isSharedCheck_6448_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_s_6434_);
                    v_a_6449_ = lean_ctor_get(v___x_6438_, 0);
                    v_a_6450_ = lean_ctor_get(v___x_6438_, 1);
                    v_isSharedCheck_6457_ = (!lean_is_exclusive(v___x_6438_)) as u8;
                    if v_isSharedCheck_6457_ == 0 {
                        v___x_6452_ = v___x_6438_;
                        v_isShared_6453_ = v_isSharedCheck_6457_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6450_);
                        lean_inc(v_a_6449_);
                        lean_dec(v___x_6438_);
                        v___x_6452_ = lean_box(0);
                        v_isShared_6453_ = v_isSharedCheck_6457_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6444_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6444_, 0, v_s_6434_);
                lean_ctor_set(v___x_6444_, 1, v_a_6439_);
                if v_isShared_6443_ == 0 {
                    lean_ctor_set(v___x_6442_, 0, v___x_6444_);
                    v___x_6446_ = v___x_6442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6447_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6447_, 0, v___x_6444_);
                    lean_ctor_set(v_reuseFailAlloc_6447_, 1, v_a_6440_);
                    v___x_6446_ = v_reuseFailAlloc_6447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6446_;
            }
            3 => {
                if v_isShared_6453_ == 0 {
                    v___x_6455_ = v___x_6452_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6456_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6449_);
                    lean_ctor_set(v_reuseFailAlloc_6456_, 1, v_a_6450_);
                    v___x_6455_ = v_reuseFailAlloc_6456_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_VerRange_parse(mut v_s_6458_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: u8 = 0;
    let mut v___x_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6468_: u8 = 0;
    let mut v___x_6469_: u8 = 0;
    let mut v_tail_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6478_: u8 = 0;
    let mut v_a_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6459_ = lean_unsigned_to_nat(0);
                v___x_6460_ = lean_string_utf8_byte_size(v_s_6458_);
                v___x_6461_ = 1;
                v___x_6462_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM___closed__0;
                lean_inc_ref(v_s_6458_);
                v___x_6463_ = l___private_Lake_Util_Version_0__Lake_VerRange_parseM_go(
                    v_s_6458_,
                    v___x_6461_,
                    v___x_6462_,
                    v___x_6462_,
                    v___x_6459_,
                );
                if lean_obj_tag(v___x_6463_) == 0 {
                    v_a_6464_ = lean_ctor_get(v___x_6463_, 0);
                    v_a_6465_ = lean_ctor_get(v___x_6463_, 1);
                    v_isSharedCheck_6478_ = (!lean_is_exclusive(v___x_6463_)) as u8;
                    if v_isSharedCheck_6478_ == 0 {
                        v___x_6467_ = v___x_6463_;
                        v_isShared_6468_ = v_isSharedCheck_6478_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6465_);
                        lean_inc(v_a_6464_);
                        lean_dec(v___x_6463_);
                        v___x_6467_ = lean_box(0);
                        v_isShared_6468_ = v_isSharedCheck_6478_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_s_6458_);
                    v_a_6479_ = lean_ctor_get(v___x_6463_, 0);
                    lean_inc(v_a_6479_);
                    lean_dec_ref_known(v___x_6463_, 2);
                    v___x_6480_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6480_, 0, v_a_6479_);
                    return v___x_6480_;
                }
            }
            1 => {
                v___x_6469_ = lean_nat_dec_eq(v_a_6465_, v___x_6460_);
                if v___x_6469_ == 0 {
                    lean_del_object(v___x_6467_);
                    lean_dec(v_a_6464_);
                    v_tail_6470_ = lean_string_utf8_extract(v_s_6458_, v_a_6465_, v___x_6460_);
                    lean_dec(v_a_6465_);
                    lean_dec_ref(v_s_6458_);
                    v___x_6471_ =
                        l___private_Lake_Util_Version_0__Lake_runVerParse___redArg___closed__0;
                    v___x_6472_ = lean_string_append(v___x_6471_, v_tail_6470_);
                    lean_dec_ref(v_tail_6470_);
                    v___x_6473_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6473_, 0, v___x_6472_);
                    return v___x_6473_;
                } else {
                    lean_dec(v_a_6465_);
                    if v_isShared_6468_ == 0 {
                        lean_ctor_set(v___x_6467_, 1, v_a_6464_);
                        lean_ctor_set(v___x_6467_, 0, v_s_6458_);
                        v___x_6475_ = v___x_6467_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6477_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6477_, 0, v_s_6458_);
                        lean_ctor_set(v_reuseFailAlloc_6477_, 1, v_a_6464_);
                        v___x_6475_ = v_reuseFailAlloc_6477_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6476_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6476_, 0, v___x_6475_);
                return v___x_6476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(
    mut v_ver_6481_: *mut LeanObject,
    mut v_as_6482_: *mut LeanObject,
    mut v_i_6483_: usize,
    mut v_stop_6484_: usize,
) -> u8 {
    let mut v___x_6485_: u8 = 0;
    let mut v___x_6486_: u8 = 0;
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: u8 = 0;
    let mut v___x_6489_: usize = 0;
    let mut v___x_6490_: usize = 0;
    let mut v___x_6492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6485_ = lean_usize_dec_eq(v_i_6483_, v_stop_6484_);
                if v___x_6485_ == 0 {
                    v___x_6486_ = 1;
                    v___x_6487_ = lean_array_uget_borrowed(v_as_6482_, v_i_6483_);
                    v___x_6488_ = l_Lake_VerComparator_test(v___x_6487_, v_ver_6481_);
                    if v___x_6488_ == 0 {
                        return v___x_6486_;
                    } else {
                        if v___x_6485_ == 0 {
                            v___x_6489_ = 1usize;
                            v___x_6490_ = lean_usize_add(v_i_6483_, v___x_6489_);
                            v_i_6483_ = v___x_6490_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_6486_;
                        }
                    }
                } else {
                    v___x_6492_ = 0;
                    return v___x_6492_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0___boxed(
    mut v_ver_6493_: *mut LeanObject,
    mut v_as_6494_: *mut LeanObject,
    mut v_i_6495_: *mut LeanObject,
    mut v_stop_6496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6497_: usize = 0;
    let mut v_stop_boxed_6498_: usize = 0;
    let mut v_res_6499_: u8 = 0;
    let mut v_r_6500_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6497_ = lean_unbox_usize(v_i_6495_);
    lean_dec(v_i_6495_);
    v_stop_boxed_6498_ = lean_unbox_usize(v_stop_6496_);
    lean_dec(v_stop_6496_);
    v_res_6499_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_6493_, v_as_6494_, v_i_boxed_6497_, v_stop_boxed_6498_);
    lean_dec_ref(v_as_6494_);
    lean_dec_ref(v_ver_6493_);
    v_r_6500_ = lean_box((v_res_6499_) as usize);
    return v_r_6500_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(
    mut v_ver_6501_: *mut LeanObject,
    mut v_as_6502_: *mut LeanObject,
    mut v_i_6503_: usize,
    mut v_stop_6504_: usize,
) -> u8 {
    let mut v___x_6505_: u8 = 0;
    let mut v___x_6506_: u8 = 0;
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: u8 = 0;
    let mut v___x_6511_: usize = 0;
    let mut v___x_6512_: usize = 0;
    let mut v___x_6513_: u8 = 0;
    let mut v___x_6514_: usize = 0;
    let mut v___x_6515_: usize = 0;
    let mut v___x_6517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6505_ = lean_usize_dec_eq(v_i_6503_, v_stop_6504_);
                if v___x_6505_ == 0 {
                    v___x_6506_ = 1;
                    v___x_6507_ = lean_array_uget_borrowed(v_as_6502_, v_i_6503_);
                    v___x_6508_ = lean_unsigned_to_nat(0);
                    v___x_6509_ = lean_array_get_size(v___x_6507_);
                    v___x_6510_ = lean_nat_dec_lt(v___x_6508_, v___x_6509_);
                    if v___x_6510_ == 0 {
                        return v___x_6506_;
                    } else {
                        if v___x_6510_ == 0 {
                            return v___x_6506_;
                        } else {
                            v___x_6511_ = 0usize;
                            v___x_6512_ = lean_usize_of_nat(v___x_6509_);
                            v___x_6513_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__0(v_ver_6501_, v___x_6507_, v___x_6511_, v___x_6512_);
                            if v___x_6513_ == 0 {
                                return v___x_6506_;
                            } else {
                                if v___x_6505_ == 0 {
                                    v___x_6514_ = 1usize;
                                    v___x_6515_ = lean_usize_add(v_i_6503_, v___x_6514_);
                                    v_i_6503_ = v___x_6515_;
                                    state = 0;
                                    continue;
                                } else {
                                    return v___x_6506_;
                                }
                            }
                        }
                    }
                } else {
                    v___x_6517_ = 0;
                    return v___x_6517_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1___boxed(
    mut v_ver_6518_: *mut LeanObject,
    mut v_as_6519_: *mut LeanObject,
    mut v_i_6520_: *mut LeanObject,
    mut v_stop_6521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6522_: usize = 0;
    let mut v_stop_boxed_6523_: usize = 0;
    let mut v_res_6524_: u8 = 0;
    let mut v_r_6525_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6522_ = lean_unbox_usize(v_i_6520_);
    lean_dec(v_i_6520_);
    v_stop_boxed_6523_ = lean_unbox_usize(v_stop_6521_);
    lean_dec(v_stop_6521_);
    v_res_6524_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_6518_, v_as_6519_, v_i_boxed_6522_, v_stop_boxed_6523_);
    lean_dec_ref(v_as_6519_);
    lean_dec_ref(v_ver_6518_);
    v_r_6525_ = lean_box((v_res_6524_) as usize);
    return v_r_6525_;
}
pub unsafe fn l_Lake_VerRange_test(
    mut v_self_6526_: *mut LeanObject,
    mut v_ver_6527_: *mut LeanObject,
) -> u8 {
    let mut v_clauses_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: u8 = 0;
    v_clauses_6528_ = lean_ctor_get(v_self_6526_, 1);
    v___x_6529_ = lean_unsigned_to_nat(0);
    v___x_6530_ = lean_array_get_size(v_clauses_6528_);
    v___x_6531_ = lean_nat_dec_lt(v___x_6529_, v___x_6530_);
    if v___x_6531_ == 0 {
        return v___x_6531_;
    } else {
        if v___x_6531_ == 0 {
            return v___x_6531_;
        } else {
            let mut v___x_6532_: usize = 0;
            let mut v___x_6533_: usize = 0;
            let mut v___x_6534_: u8 = 0;
            v___x_6532_ = 0usize;
            v___x_6533_ = lean_usize_of_nat(v___x_6530_);
            v___x_6534_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lake_VerRange_test_spec__1(v_ver_6527_, v_clauses_6528_, v___x_6532_, v___x_6533_);
            return v___x_6534_;
        }
    }
}
pub unsafe fn l_Lake_VerRange_test___boxed(
    mut v_self_6535_: *mut LeanObject,
    mut v_ver_6536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6537_: u8 = 0;
    let mut v_r_6538_: *mut LeanObject = core::ptr::null_mut();
    v_res_6537_ = l_Lake_VerRange_test(v_self_6535_, v_ver_6536_);
    lean_dec_ref(v_ver_6536_);
    lean_dec_ref(v_self_6535_);
    v_r_6538_ = lean_box((v_res_6537_) as usize);
    return v_r_6538_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Version(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Date(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_SemVerCore_instLT = _init_l_Lake_SemVerCore_instLT();
    lean_mark_persistent(l_Lake_SemVerCore_instLT);
    l_Lake_SemVerCore_instLE = _init_l_Lake_SemVerCore_instLE();
    lean_mark_persistent(l_Lake_SemVerCore_instLE);
    l_Lake_StdVer_instLT = _init_l_Lake_StdVer_instLT();
    lean_mark_persistent(l_Lake_StdVer_instLT);
    l_Lake_StdVer_instLE = _init_l_Lake_StdVer_instLE();
    lean_mark_persistent(l_Lake_StdVer_instLE);
    l_Lake_ToolchainVer_instLT = _init_l_Lake_ToolchainVer_instLT();
    lean_mark_persistent(l_Lake_ToolchainVer_instLT);
    l_Lake_ToolchainVer_instLE = _init_l_Lake_ToolchainVer_instLE();
    lean_mark_persistent(l_Lake_ToolchainVer_instLE);
    l_Lake_instInhabitedComparatorOp_default = _init_l_Lake_instInhabitedComparatorOp_default();
    l_Lake_instInhabitedComparatorOp = _init_l_Lake_instInhabitedComparatorOp();
    l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie =
        _init_l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie();
    lean_mark_persistent(l___private_Lake_Util_Version_0__Lake_ComparatorOp_parseM_trie);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Version(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Version(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_Date(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Control_Do(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Trie(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Version(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Version(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Version(builtin);
}
